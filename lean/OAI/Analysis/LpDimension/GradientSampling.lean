import OAI.Analysis.LpDimension.StableLaw

namespace OAI

noncomputable section
open MeasureTheory Filter Matrix NormedSpace Metric Module Set ProbabilityTheory
open scoped BigOperators Topology Matrix Matrix.Norms.Operator ENNReal NNReal RealInnerProductSpace
universe u uE uV uΩ uι

namespace SubpolynomialLp

lemma below_error_algebra (p c T H : ℝ) (hT : 0 < T) (hH : 0 < H) :
    (p*(T/H)^(p-1))*H*((2*c*2^p)*(1+1/(p-1))*T^(1-p))+
      (T/H)^(p-2)*(96*c*T^(2-p)) =
    (p*(2*c*2^p)*(1+1/(p-1))+96*c)*H^(2-p) := by
  have h₁ : T^(p-1)*T^(1-p) = 1 := by rw [← Real.rpow_add hT]; simp
  have h₂ : T^(p-2)*T^(2-p) = 1 := by rw [← Real.rpow_add hT]; simp
  have h₃ : H/H^(p-1) = H^(2-p) := by
    conv_lhs => lhs; rw [← Real.rpow_one H]
    rw [← Real.rpow_sub hH]
    congr 1
    ring
  have h₄ : 1/H^(p-2) = H^(2-p) := by rw [one_div, ← Real.rpow_neg hH.le]; congr 1; ring
  rw [Real.div_rpow hT.le hH.le, Real.div_rpow hT.le hH.le]
  calc
    _ = (p*(2*c*2^p)*(1+1/(p-1)))*(H/H^(p-1))*(T^(p-1)*T^(1-p))+
      (96*c)*(1/H^(p-2))*(T^(p-2)*T^(2-p)) := by ring
    _ = _ := by rw [h₁,h₂,h₃,h₄]; ring

lemma stable_gradient_weighted {ι : Type uι} {E : Type uE} {V : Type uV} [Fintype ι]
    [Fintype E] [Fintype V] [DecidableEq E] [DecidableEq V] [Nonempty E]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (p c : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hc : 0 < c) (hcf : ∀ t : ℝ, charFun μ t = Complex.exp ((-c*|t|^p:ℝ):ℂ))
    (src dst : E → V) (δ lam : E → ℝ) (hδ : ∀ e, 0 < δ e)
    (hlam : ∀ e, 0 < lam e) (hls : ∑ e, lam e = 1)
    (hcard : 2 ≤ Fintype.card V)
    (hinc : ∀ i : V, ∃ e, src e = i ∨ dst e = i)
    (hconn : ∀ i j : V, i ≠ j → ∃ e,
      (src e = i ∧ dst e = j) ∨ (src e = j ∧ dst e = i))
    (g : ι → E → ℝ) (hgV : ∀ i, ∃ z, (normalizedGradient src dst δ).mulVec z = g i)
    (hg : ∀ e, ∑ i, |g i e|^p = 1)
    (T : ℝ) (hT : 0 < T) :
    let H := 4*Real.log (Fintype.card V:ℝ)
    ∃ F : (ι → ℝ) → E → ℝ, Measurable F ∧
      (∀ x, ∃ z, (normalizedGradient src dst δ).mulVec z = F x) ∧
      (∀ x e, |F x e| ≤ H*T) ∧
      (∑ e, lam e*|(∫ x, |F x e|^p ∂Measure.pi (fun _ : ι => μ))-
        (∫ x, (min |x| (T/H))^p ∂μ)|) ≤
        (p*(2*c*2^p)*(1+1/(p-1))+96*c)*H^(2-p) := by
  classical
  dsimp only
  let A := normalizedGradient src dst δ
  let V' : Submodule ℝ (E → ℝ) := LinearMap.range A.mulVecLin
  have hgV' (i : ι) : g i ∈ V' := hgV i
  obtain ⟨Y,hYm,hYV,hYLaw⟩ := stable_joint_gradient μ p c (by linarith) hcf V' g hgV' hg
  have hH : 0 < 4*Real.log (Fintype.card V:ℝ) := by
    apply mul_pos (by norm_num)
    exact Real.log_pos (by exact_mod_cast (by omega : 1 < Fintype.card V))
  obtain ⟨F,hFm,hFV,hFb,hFerr⟩ := stable_retraction_moments
    (Measure.pi (fun _ : ι => μ)) μ p c hp hp2 hc
    (fun t => by rw [hcf, Complex.exp_ofReal_re])
    src dst δ lam hδ hlam hls hcard hinc hconn Y hYm hYV hYLaw T
    (T/(4*Real.log (Fintype.card V:ℝ))) hT (div_pos hT hH)
  refine ⟨F,hFm,hFV,hFb,?_⟩
  rwa [below_error_algebra p c T _ hT hH] at hFerr


lemma moment_integral_mem {Ω : Type uΩ} {E : Type uE} [MeasurableSpace Ω] [Fintype E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (S : Set (E → ℝ)) (F : Ω → E → ℝ)
    (hF : Measurable F) (hFS : ∀ x, F x ∈ S) (M : ℝ)
    (hM : ∀ x e, ‖F x e‖ ≤ M) :
    (fun e => ∫ x, F x e ∂μ) ∈ closedConvexHull ℝ S := by
  have hi (e : E) : Integrable (fun x => F x e) μ :=
    Integrable.of_bound ((measurable_pi_apply e).comp hF).aestronglyMeasurable M (Filter.Eventually.of_forall (fun x => hM x e))
  have hiv : Integrable F μ := integrable_pi_iff.mpr hi
  have hh := convex_closedConvexHull.integral_mem (isClosed_closedConvexHull (𝕜 := ℝ) (s := S))
    (Filter.Eventually.of_forall fun x => subset_closedConvexHull (hFS x)) hiv
  have he : (∫ x, F x ∂μ) = fun e => ∫ x, F x e ∂μ := by
    ext e
    exact ((ContinuousLinearMap.proj e : (E → ℝ) →L[ℝ] ℝ).integral_comp_comm hiv).symm
  rwa [he] at hh

lemma weighted_gradient_samples {Ω : Type uΩ} {E : Type uE} {V : Type uV} [MeasurableSpace Ω]
    [Fintype E] [Fintype V] [Nonempty E] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Matrix E V ℝ) (p K b ε : ℝ) (hp : 0 < p) (hK : 0 ≤ K) (hε : 0 < ε)
    (hw : ∀ w : E → ℝ, (∀ e, 0 < w e) → (∑ e, w e)=1 →
      ∃ F : Ω → E → ℝ, Measurable F ∧
        (∀ x, ∃ z, A.mulVec z = F x) ∧ (∀ x e, |F x e| ≤ K) ∧
        (∑ e, w e*|(∫ x, |F x e|^p ∂μ)-b|) ≤ ε)
    (d : ℕ) (hd : 0 < d)
    (hprob : (2*Fintype.card E:ℝ)*Real.exp (-((d:ℝ)*ε)^2/(2*d*(K^p/2)^2)) < 1) :
    ∃ z : Fin d → V → ℝ, ∀ e,
      |(∑ a, |A.mulVec (z a) e|^p)/(d:ℝ)-b| < 3*ε := by
  classical
  let S : Set (E → ℝ) := {m | ∃ z : V → ℝ,
    (∀ e, |A.mulVec z e| ≤ K) ∧ ∀ e, m e = |A.mulVec z e|^p}
  have hS : ∀ m ∈ S, ∀ e, m e ∈ Set.Icc 0 (K^p) := by
    rintro m ⟨z,hz,rflz⟩ e
    rw [rflz e]
    exact ⟨Real.rpow_nonneg (abs_nonneg _) _, Real.rpow_le_rpow (abs_nonneg _) (hz e) hp.le⟩
  have hw' : ∀ w : E → ℝ, (∀ e, 0 < w e) → (∑ e, w e)=1 →
      ∃ m ∈ closedConvexHull ℝ S, (∑ e, w e*|m e-b|) ≤ ε := by
    intro w hw0 hws
    obtain ⟨F,hFm,hFV,hFb,hFe⟩ := hw w hw0 hws
    refine ⟨fun e => ∫ x, |F x e|^p ∂μ, ?_, hFe⟩
    refine moment_integral_mem μ S (fun x e => |F x e|^p) (by fun_prop) ?_ (K^p) ?_
    · intro x
      obtain ⟨z,hz⟩ := hFV x
      exact ⟨z, by simpa only [hz] using hFb x, fun e => by rw [hz]⟩
    · intro x e
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
      exact Real.rpow_le_rpow (abs_nonneg _) (hFb x e) hp.le
  obtain ⟨m,hm,hme⟩ := weighted_moments_samples (S := S) (K^p)
    (Real.rpow_nonneg hK _) hS b ε hε hw' d hd hprob
  choose z hz hmz using hm
  refine ⟨z,fun e => ?_⟩
  simpa only [hmz] using hme e

instance pairIndexDecidableEq (n : ℕ) : DecidableEq (PairIndex n) := by
  unfold PairIndex
  infer_instance

lemma pairIndex_nonempty (n : ℕ) (hn : 2 ≤ n) : Nonempty (PairIndex n) :=
  ⟨⟨(⟨0,by omega⟩,⟨1,by omega⟩),by change (0:ℕ) < 1; omega⟩⟩

lemma pairIndex_connected (n : ℕ) (i j : Fin n) (hij : i ≠ j) :
    ∃ e : PairIndex n, (e.val.1 = i ∧ e.val.2 = j) ∨ (e.val.1 = j ∧ e.val.2 = i) := by
  rcases lt_or_gt_of_ne hij with h|h
  · exact ⟨⟨(i,j),h⟩,Or.inl ⟨rfl,rfl⟩⟩
  · exact ⟨⟨(j,i),h⟩,Or.inr ⟨rfl,rfl⟩⟩

lemma pairIndex_incident (n : ℕ) (hn : 2 ≤ n) (i : Fin n) :
    ∃ e : PairIndex n, e.val.1 = i ∨ e.val.2 = i := by
  let j : Fin n := if i.val = 0 then ⟨1,by omega⟩ else ⟨0,by omega⟩
  have hij : i ≠ j := by
    intro h
    have hh := congrArg Fin.val h
    dsimp [j] at hh
    split_ifs at hh with hi
    · change i.val = 1 at hh
      omega
    · change i.val = 0 at hh
      exact hi hh
  obtain ⟨e,h|h⟩ := pairIndex_connected n i j hij
  · exact ⟨e,Or.inl h.1⟩
  · exact ⟨e,Or.inr h.2⟩

lemma normalizedGradient_apply {E : Type uE} {V : Type uV} [Fintype E] [Fintype V]
    [DecidableEq E] [DecidableEq V] (src dst : E → V) (δ : E → ℝ)
    (z : V → ℝ) (e : E) :
    (normalizedGradient src dst δ).mulVec z e = (z (src e)-z (dst e))/δ e := by
  rw [normalizedGradient, ← Matrix.mulVec_mulVec, Matrix.mulVec_diagonal, incidence_mulVec]
  simp [div_eq_mul_inv, mul_comm]

lemma normalized_coordinate_gradient (p : ℝ) (hp : 0 < p) {n k : ℕ}
    (y : Fin n → Fin k → ℝ) (δ : PairIndex n → ℝ) (hδ : ∀ e, 0 < δ e)
    (hy : ∀ e : PairIndex n, coordinateDistance p (y e.val.1) (y e.val.2) = δ e) :
    ∀ e : PairIndex n, ∑ a : Fin k,
      |(normalizedGradient (fun e : PairIndex n => e.val.1) (fun e => e.val.2) δ).mulVec
        (fun i => y i a) e|^p = 1 := by
  classical
  intro e
  simp_rw [normalizedGradient_apply, abs_div, abs_of_pos (hδ e),
    Real.div_rpow (abs_nonneg _) (hδ e).le]
  rw [← Finset.sum_div]
  have hh := congrArg (fun t : ℝ => t^p) (hy e)
  rw [coordinateDistance_rpow p hp] at hh
  change (∑ a, |y e.val.1 a-y e.val.2 a|^p) = (δ e)^p at hh
  rw [hh, div_self (Real.rpow_pos_of_pos (hδ e) _).ne']

lemma sampled_labels_embedding (p D b ε : ℝ) (hp : 0 < p) (hD : 0 ≤ D)
    (hb : 0 < b-3*ε) (hDb : b+3*ε ≤ D^p*(b-3*ε))
    {n d : ℕ} (hd : 0 < d) (δ : PairIndex n → ℝ) (hδ : ∀ e, 0 < δ e)
    (z : Fin d → Fin n → ℝ)
    (hz : ∀ e : PairIndex n,
      |(∑ a, |(normalizedGradient (fun e : PairIndex n => e.val.1) (fun e => e.val.2) δ).mulVec
        (z a) e|^p)/(d:ℝ)-b| < 3*ε) :
    ∃ s : ℝ, 0 < s ∧ ∀ e : PairIndex n,
      s*δ e ≤ coordinateDistance p (fun a => z a e.val.1) (fun a => z a e.val.2) ∧
      coordinateDistance p (fun a => z a e.val.1) (fun a => z a e.val.2) ≤ D*s*δ e := by
  classical
  have hd0 : (0:ℝ) < d := by exact_mod_cast hd
  let s := ((d:ℝ)*(b-3*ε))^(1/p)
  have hs : 0 < s := Real.rpow_pos_of_pos (mul_pos hd0 hb) _
  have hsp : s^p = (d:ℝ)*(b-3*ε) := by
    dsimp [s]
    rw [← Real.rpow_mul (mul_pos hd0 hb).le, one_div_mul_cancel hp.ne', Real.rpow_one]
  refine ⟨s,hs,fun e => ?_⟩
  let m := ∑ a, |(normalizedGradient (fun e : PairIndex n => e.val.1) (fun e => e.val.2) δ).mulVec (z a) e|^p
  have hm : (d:ℝ)*(b-3*ε) ≤ m ∧ m ≤ (d:ℝ)*(b+3*ε) := by
    have he := abs_lt.mp (hz e)
    constructor
    · have hh : b-3*ε ≤ m/d := by dsimp [m]; linarith [he.1]
      simpa only [mul_comm] using (le_div_iff₀ hd0).mp hh
    · have hh : m/d ≤ b+3*ε := by dsimp [m]; linarith [he.2]
      simpa only [mul_comm] using (div_le_iff₀ hd0).mp hh
  have hm0 : 0 ≤ m := Finset.sum_nonneg (fun _ _ => Real.rpow_nonneg (abs_nonneg _) _)
  have hsum : (∑ a, |z a e.val.1-z a e.val.2|^p) = (δ e)^p*m := by
    dsimp [m]
    simp_rw [normalizedGradient_apply, abs_div, abs_of_pos (hδ e), Real.div_rpow (abs_nonneg _) (hδ e).le]
    rw [← Finset.sum_div, mul_div_cancel₀ _ (Real.rpow_pos_of_pos (hδ e) p).ne']
  have hdist : coordinateDistance p (fun a => z a e.val.1) (fun a => z a e.val.2) = δ e*m^(1/p) := by
    rw [coordinateDistance, hsum, Real.mul_rpow (Real.rpow_nonneg (hδ e).le _) hm0,
      ← Real.rpow_mul (hδ e).le, mul_one_div_cancel hp.ne', Real.rpow_one]
  rw [hdist]
  constructor
  · have hh := Real.rpow_le_rpow (mul_pos hd0 hb).le hm.1 (by positivity : 0 ≤ 1/p)
    dsimp [s] at *
    nlinarith [mul_nonneg (hδ e).le (sub_nonneg.mpr hh)]
  · have hh : m ≤ (D*s)^p := by
      rw [Real.mul_rpow hD hs.le, hsp]
      have ht := mul_le_mul_of_nonneg_left hDb hd0.le
      nlinarith [hm.2]
    have ht := Real.rpow_le_rpow hm0 hh (by positivity : 0 ≤ 1/p)
    rw [← Real.rpow_mul (mul_nonneg hD hs.le), mul_one_div_cancel hp.ne', Real.rpow_one] at ht
    nlinarith [mul_nonneg (hδ e).le (sub_nonneg.mpr ht)]


lemma distortion_ratio (p D : ℝ) (hp : 0 < p) (hD : 1 < D) :
    ∃ R : ℝ, 3 < R ∧ ∀ b ε : ℝ, 0 < ε → R*ε ≤ b →
      0 < b-3*ε ∧ b+3*ε ≤ D^p*(b-3*ε) := by
  have hd : 1 < D^p := Real.one_lt_rpow hD hp
  let R := 3+6/(D^p-1)
  have hR : 3 < R := by
    have hh : 0 < 6/(D^p-1) := by positivity
    dsimp [R]; linarith
  have hReq : R*(D^p-1) = 3*(D^p+1) := by
    dsimp [R]
    field_simp [show D^p-1 ≠ 0 by linarith]
    ring
  refine ⟨R,hR,fun b ε hε hb => ⟨?_,?_⟩⟩
  · have hh := mul_lt_mul_of_pos_right hR hε
    linarith
  · have hh := mul_le_mul_of_nonneg_right hb (show 0 ≤ D^p-1 by linarith)
    nlinarith

end SubpolynomialLp

end

end OAI
