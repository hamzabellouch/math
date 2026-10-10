import OAI.Analysis.LpDimension.HeatLocalization

namespace OAI

noncomputable section
open MeasureTheory Filter Matrix NormedSpace
open scoped BigOperators Topology Matrix Matrix.Norms.Operator
universe u uE uV

namespace SubpolynomialLp

section GraphProjection
variable {E : Type uE} {V : Type uV} [Fintype E] [Fintype V] [DecidableEq E] [DecidableEq V]

def conductorMatrix (src dst : E → V) (c : E → ℝ) : Matrix E V ℝ :=
  diagonal (fun e => Real.sqrt (c e)) * incidence src dst

omit [Fintype V] in
lemma conductorMatrix_gram (src dst : E → V) (c : E → ℝ) (hc : ∀ e, 0 ≤ c e) :
    (conductorMatrix src dst c).transpose * conductorMatrix src dst c = laplacianMatrix src dst c := by
  have he : diagonal (fun e => Real.sqrt (c e)) * diagonal (fun e => Real.sqrt (c e)) = diagonal c := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext e
    exact Real.mul_self_sqrt (hc e)
  unfold conductorMatrix laplacianMatrix
  rw [Matrix.transpose_mul, Matrix.diagonal_transpose]
  calc
    _ = (incidence src dst).transpose *
        (diagonal (fun e => Real.sqrt (c e)) * diagonal (fun e => Real.sqrt (c e))) * incidence src dst := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [he]

lemma conductorMatrix_mul_apply (src dst : E → V) (c : E → ℝ) (K : Matrix V V ℝ) (e : E) (v : V) :
    (conductorMatrix src dst c * K) e v = Real.sqrt (c e) * (K (src e) v - K (dst e) v) := by
  rw [conductorMatrix, Matrix.mul_assoc, Matrix.diagonal_mul]
  congr 1
  exact incidence_mulVec src dst (fun i => K i v) e

omit [DecidableEq E] in
lemma gram_heat_weighted (R : Matrix E V ℝ) (d : V → ℝ) (t : ℝ) :
    (R * diagonal d) * exp (-t • ((R * diagonal d).conjTranspose * (R * diagonal d))) *
      (R * diagonal d).transpose =
    R * weightedHeatKernel (R.transpose * R) d t * R.transpose := by
  have he : (R * diagonal d).conjTranspose * (R * diagonal d) =
      symmetricGenerator (R.transpose * R) d := by
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_mul, Matrix.diagonal_transpose]
    simp only [symmetricGenerator, Matrix.mul_assoc]
  rw [he]
  simp only [weightedHeatKernel, Matrix.transpose_mul, Matrix.diagonal_transpose, Matrix.mul_assoc]

omit [DecidableEq E] in
lemma gram_heat_twice (R : Matrix E V ℝ) (d μ : V → ℝ)
    (hrel : ∀ i, d i * μ i * d i = 1) (t : ℝ) (e f : E) :
    ((R * diagonal d) * exp (-(2*t) • ((R * diagonal d).conjTranspose * (R * diagonal d))) *
      (R * diagonal d).transpose) e f =
      ∑ v, μ v * (R * weightedHeatKernel (R.transpose * R) d t) e v *
        (R * weightedHeatKernel (R.transpose * R) d t) f v := by
  rw [gram_heat_weighted, two_mul, weightedHeatKernel_semigroup _ _ _ hrel]
  have hL : (R.transpose * R).IsSymm := by
    simp only [Matrix.IsSymm, Matrix.transpose_mul, Matrix.transpose_transpose]
  have he : R * (weightedHeatKernel (R.transpose * R) d t * diagonal μ *
      weightedHeatKernel (R.transpose * R) d t) * R.transpose =
      (R * weightedHeatKernel (R.transpose * R) d t) * diagonal μ *
        (R * weightedHeatKernel (R.transpose * R) d t).transpose := by
    rw [Matrix.transpose_mul, (weightedHeatKernel_symmetric _ hL d t).eq]
    simp only [Matrix.mul_assoc]
  rw [he, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro v _
  ring

omit [Fintype V] [DecidableEq E] in
lemma vertexWeight_pos (src dst : E → V) (w : E → ℝ) (hw : ∀ e, 0 < w e)
    (i : V) (hi : ∃ e, src e = i ∨ dst e = i) : 0 < vertexWeight src dst w i := by
  have hn (p : E → Prop) [DecidablePred p] : 0 ≤ ∑ e, if p e then (w e)^2 else 0 := by
    apply Finset.sum_nonneg
    intro e _
    split_ifs <;> positivity
  have hp (p : E → Prop) [DecidablePred p] (e : E) (he : p e) :
      0 < ∑ e, if p e then (w e)^2 else 0 := by
    apply Finset.sum_pos' (fun e _ => by split_ifs <;> positivity)
    exact ⟨e, Finset.mem_univ e, by simpa only [ite_eq_left he] using sq_pos_of_pos (hw e)⟩
  obtain ⟨e, he | he⟩ := hi
  · exact add_pos_of_pos_of_nonneg (hp _ e he) (hn _)
  · exact add_pos_of_nonneg_of_pos (hn _) (hp _ e he)

lemma graph_localization_positive (src dst : E → V) (c w : E → ℝ)
    (hc : ∀ e, 0 < c e) (hw : ∀ e, 0 < w e)
    (hinc : ∀ i : V, ∃ e, src e = i ∨ dst e = i)
    (hconn : ∀ i j : V, i ≠ j → ∃ e,
      (src e = i ∧ dst e = j) ∨ (src e = j ∧ dst e = i))
    (hW : 0 < ∑ e, (w e)^2) :
    (∑ e, ∑ f, w e * w f * |gramProjection (conductorMatrix src dst c) e f|) ≤
      2 * Real.log (Fintype.card V : ℝ) * ∑ e, (w e)^2 := by
  let R := conductorMatrix src dst c
  let μ := vertexMass src dst w
  let d : V → ℝ := fun i => (Real.sqrt (μ i))⁻¹
  let A := R * diagonal d
  let L := laplacianMatrix src dst c
  let K := weightedHeatKernel L d
  let F : ℝ → E → E → ℝ := fun t e f =>
    (A * exp (-(2*t) • (A.conjTranspose * A)) * A.transpose) e f
  let I : ℝ → V → ℝ := fun t v => electricalEnergy src dst c (fun i => K t i v)
  have hμ (i : V) : 0 < μ i :=
    div_pos (vertexWeight_pos src dst w hw i (hinc i)) (by positivity)
  have hd (i : V) : 0 < d i := inv_pos.mpr (Real.sqrt_pos.mpr (hμ i))
  have hrel (i : V) : μ i * (d i * d i) = 1 := by
    dsimp only [d]
    rw [← mul_inv, Real.mul_self_sqrt (hμ i).le, mul_inv_cancel₀ (hμ i).ne']
  have hrel' (i : V) : d i * μ i * d i = 1 := by nlinarith [hrel i]
  have hsum : ∑ i, μ i = 1 := vertexMass_sum src dst w hW
  have hR : R.transpose * R = L := conductorMatrix_gram src dst c (fun e => (hc e).le)
  have hrep (e f : E) : gramProjection R e f = 2 * ∫ t in Set.Ioi (0 : ℝ), F t e f := by
    have hh := integral_comp_mul_left_Ioi' (fun t : ℝ =>
      (A * exp (-t • (A.conjTranspose * A)) * A.transpose) e f) 0 (by norm_num : (0 : ℝ) < 2)
    have he := (gramProjection_heat_integral A e f).2
    rw [mul_zero] at hh
    rw [he] at hh
    have hQ : gramProjection A = gramProjection R :=
      gramProjection_right_diagonal R d (fun i => (hd i).ne')
    rw [hQ] at hh
    exact hh.symm
  have hiF (e f : E) : IntegrableOn (fun t => F t e f) (Set.Ioi 0) := by
    have hh := (integrableOn_Ioi_comp_mul_left_iff (fun t : ℝ =>
      (A * exp (-t • (A.conjTranspose * A)) * A.transpose) e f) 0 (by norm_num : (0 : ℝ) < 2)).2
    apply hh
    simpa only [mul_zero] using (gramProjection_heat_integral A e f).1
  have hI (v : V) : IntegrableOn (fun t => I t v) (Set.Ioi 0) ∧
      (∫ t in Set.Ioi (0 : ℝ), I t v) = Real.log (1 / μ v) :=
    graphHeat_entropy_integral src dst c μ d hc hμ hd hrel hsum hconn v
  have hb (t : ℝ) (ht : 0 < t) :
      (∑ e, ∑ f, w e * w f * |F t e f|) ≤ (∑ e, (w e)^2) * ∑ v, μ v * I t v := by
    have heF (e f : E) : F t e f = ∑ v, μ v * (R * K t) e v * (R * K t) f v := by
      have hh := gram_heat_twice R d μ hrel' t e f
      rw [hR] at hh
      exact hh
    have henergy (v : V) : (∑ e, w e * |(R * K t) e v|)^2 ≤ I t v * ∑ e, (w e)^2 := by
      have hpos (i : V) : 0 < K t i v := weightedHeatKernel_pos L d hd
        (fun i j hij => laplacianMatrix_offdiag_neg src dst c hc hij (hconn i j hij)) t ht i v
      have hh := heat_cauchy_schwarz src dst c w (fun i => K t i v) (fun e => (hc e).le)
        hpos hW (graphHeat_mass src dst c μ d hμ hrel t v)
      exact le_of_eq_of_le (by
        congr 1
        apply Finset.sum_congr rfl
        intro e _
        rw [conductorMatrix_mul_apply, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
        ring) hh
    simp_rw [heF]
    calc
      _ ≤ ∑ v, μ v * (∑ e, w e * |(R * K t) e v|)^2 :=
        sum_abs_outer_le μ w (R * K t) (fun v => (hμ v).le) (fun e => (hw e).le)
      _ ≤ ∑ v, μ v * (I t v * ∑ e, (w e)^2) :=
        Finset.sum_le_sum (fun v _ => mul_le_mul_of_nonneg_left (henergy v) (hμ v).le)
      _ = _ := by simp only [← mul_assoc, ← Finset.sum_mul]; ring
  have hh := localization_integral_bound (gramProjection R) F I μ w (∑ e, (w e)^2)
    (fun e => (hw e).le) hrep hiF (fun v => (hI v).1) (fun v => (hI v).2) hb
  have he := mul_le_mul_of_nonneg_left (entropy_le_log_card μ hμ hsum)
    (show 0 ≤ 2 * ∑ e, (w e)^2 by positivity)
  exact hh.trans (by convert he using 1; ring)

lemma graph_localization_nonneg (src dst : E → V) (c w : E → ℝ)
    (hc : ∀ e, 0 < c e) (hw : ∀ e, 0 ≤ w e)
    (hinc : ∀ i : V, ∃ e, src e = i ∨ dst e = i)
    (hconn : ∀ i j : V, i ≠ j → ∃ e,
      (src e = i ∧ dst e = j) ∨ (src e = j ∧ dst e = i)) :
    (∑ e, ∑ f, w e * w f * |gramProjection (conductorMatrix src dst c) e f|) ≤
      2 * Real.log (Fintype.card V : ℝ) * ∑ e, (w e)^2 := by
  cases isEmpty_or_nonempty E with
  | inl hE => simp
  | inr hE =>
    let wn : ℕ → E → ℝ := fun n e => w e + 1 / ((n : ℝ) + 1)
    have hp (n : ℕ) (e : E) : 0 < wn n e := by
      dsimp [wn]
      exact add_pos_of_nonneg_of_pos (hw e) (by positivity)
    have ht : Tendsto wn atTop (𝓝 w) := by
      apply tendsto_pi_nhds.mpr
      intro e
      simpa only [add_zero] using tendsto_one_div_add_atTop_nhds_zero_nat.const_add (w e)
    let f : (E → ℝ) → ℝ := fun x => ∑ e, ∑ f, x e * x f *
      |gramProjection (conductorMatrix src dst c) e f|
    let g : (E → ℝ) → ℝ := fun x => 2 * Real.log (Fintype.card V : ℝ) * ∑ e, (x e)^2
    have hf : Continuous f := by dsimp [f]; fun_prop
    have hg : Continuous g := by dsimp [g]; fun_prop
    apply le_of_tendsto_of_tendsto' ((hf.tendsto w).comp ht) ((hg.tendsto w).comp ht)
    intro n
    apply graph_localization_positive src dst c (wn n) hc (hp n) hinc hconn
    exact Finset.sum_pos (fun e _ => sq_pos_of_pos (hp n e)) Finset.univ_nonempty

lemma orthogonal_sum_sq (U : Matrix E E ℝ) (hU : U.transpose * U = 1) (x : E → ℝ) :
    ∑ i, (U *ᵥ x) i ^ 2 = ∑ i, (x i)^2 := by
  have hh : (U *ᵥ x) ⬝ᵥ (U *ᵥ x) = x ⬝ᵥ x := by
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec, hU, Matrix.vecMul_one]
  simpa only [dotProduct, sq] using hh

lemma symmetric_quadratic_bound_sq (B : Matrix E E ℝ) (hB : B.IsSymm) (H : ℝ)
    (hb : ∀ x : E → ℝ, |x ⬝ᵥ (B *ᵥ x)| ≤ H * ∑ i, (x i)^2) (x : E → ℝ) :
    (∑ i, (B *ᵥ x) i ^ 2) ≤ H^2 * ∑ i, (x i)^2 := by
  let hS : B.IsHermitian := Matrix.isHermitian_iff_isSymm.mpr hB
  let U : Matrix E E ℝ := hS.eigenvectorUnitary
  let lam : E → ℝ := hS.eigenvalues
  have hU : U.transpose * U = 1 := by
    simpa only [U, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
      using Unitary.coe_star_mul_self hS.eigenvectorUnitary
  have hU' : U * U.transpose = 1 := by
    simpa only [U, Unitary.coe_star, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using Unitary.coe_mul_star_self hS.eigenvectorUnitary
  have hs : B = U * diagonal lam * U.transpose := by
    convert hS.spectral_theorem using 1
    rw [Unitary.conjStarAlgAut_apply]
    rfl
  have hBU : B * U = U * diagonal lam := by
    rw [hs, Matrix.mul_assoc, hU, Matrix.mul_one]
  have hnorm (k : E) : ∑ i, (U i k)^2 = 1 := by
    have hh := congrFun₂ hU k k
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_eq, sq] using hh
  have hval (k : E) : |lam k| ≤ H := by
    have he : B *ᵥ (fun i => U i k) = fun i => U i k * lam k := by
      funext i
      change (B * U) i k = U i k * lam k
      rw [hBU, Matrix.mul_diagonal]
    have hh := hb (fun i => U i k)
    have hd : (fun i => U i k) ⬝ᵥ (fun i => U i k * lam k) = lam k := by
      simp only [dotProduct, ← mul_assoc, ← sq, ← Finset.sum_mul, hnorm, one_mul]
    rw [he, hd, hnorm, mul_one] at hh
    exact hh
  let y := U.transpose *ᵥ x
  have hy : ∑ i, (y i)^2 = ∑ i, (x i)^2 := by
    apply orthogonal_sum_sq
    simpa only [Matrix.transpose_transpose] using hU'
  have he : B *ᵥ x = U *ᵥ (diagonal lam *ᵥ y) := by
    rw [hs]
    simp only [Matrix.mulVec_mulVec, y, Matrix.mul_assoc]
  rw [he, orthogonal_sum_sq U hU]
  calc
    _ = ∑ i, (lam i)^2 * (y i)^2 := by simp only [Matrix.mulVec_diagonal, mul_pow]
    _ ≤ ∑ i, H^2 * (y i)^2 := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (lam i)) (hval i) 2
    _ = _ := by rw [← Finset.mul_sum, hy]


lemma graph_localization_quadratic (src dst : E → V) (c x : E → ℝ)
    (hc : ∀ e, 0 < c e)
    (hinc : ∀ i : V, ∃ e, src e = i ∨ dst e = i)
    (hconn : ∀ i j : V, i ≠ j → ∃ e,
      (src e = i ∧ dst e = j) ∨ (src e = j ∧ dst e = i)) :
    abs (∑ e, ∑ f, x e * x f * |gramProjection (conductorMatrix src dst c) e f|) ≤
      2 * Real.log (Fintype.card V : ℝ) * ∑ e, (x e)^2 := by
  calc
    _ ≤ ∑ e, abs (∑ f, x e * x f * |gramProjection (conductorMatrix src dst c) e f|) :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ e, ∑ f, abs (x e * x f * |gramProjection (conductorMatrix src dst c) e f|) :=
      Finset.sum_le_sum (fun e _ => Finset.abs_sum_le_sum_abs _ _)
    _ = ∑ e, ∑ f, |x e| * |x f| * |gramProjection (conductorMatrix src dst c) e f| := by
      simp only [abs_mul, abs_abs]
    _ ≤ _ := by
      simpa only [sq_abs] using graph_localization_nonneg src dst c (fun e => |x e|) hc
        (fun e => abs_nonneg _) hinc hconn

/-- The squared ℓ₂ form of electrical localization, for the complete graph
used by the main upper-bound construction. -/
lemma electrical_localization_complete (src dst : E → V) (c x : E → ℝ)
    (hc : ∀ e, 0 < c e)
    (hinc : ∀ i : V, ∃ e, src e = i ∨ dst e = i)
    (hconn : ∀ i j : V, i ≠ j → ∃ e,
      (src e = i ∧ dst e = j) ∨ (src e = j ∧ dst e = i)) :
    (∑ e, (∑ f, |gramProjection (conductorMatrix src dst c) e f| * x f)^2) ≤
      (2 * Real.log (Fintype.card V : ℝ))^2 * ∑ e, (x e)^2 := by
  let B : Matrix E E ℝ := fun e f => |gramProjection (conductorMatrix src dst c) e f|
  have hsym : B.IsSymm := by
    ext e f
    exact congrArg abs (congrFun₂ (gramProjection_symmetric _) e f)
  apply symmetric_quadratic_bound_sq B hsym
  intro y
  have hh := graph_localization_quadratic src dst c y hc hinc hconn
  convert hh using 1
  congr 1
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, B]
  apply Finset.sum_congr rfl
  intro e _
  apply Finset.sum_congr rfl
  intro f _
  ring

end GraphProjection

end SubpolynomialLp

end

end OAI
