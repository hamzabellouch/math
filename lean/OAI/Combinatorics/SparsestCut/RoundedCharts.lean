import OAI.Combinatorics.SparsestCut.ChartLinear

namespace OAI

universe u1 u2

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.SourceCharts
open scoped BigOperators RealInnerProductSpace
open Filter Set
noncomputable section
variable {m : ℕ} (f : PivotFamily.PFamily m) (hm : 0 < m)
local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "F" => EuclideanSpace ℝ (Fin (m^6))
def u (s : Fin (m^3)) (i : Fin (m^6)) : E := (Real.sqrt m)⁻¹ • f.g s i
def lower (m : ℕ) : ℝ := (m:ℝ)^6/(2*m)
include hm
lemma lower_pos : 0<lower m := by unfold lower; positivity
lemma energy (s : Fin (m^3)) (x : E) : lower m*‖x‖^2≤‖FrameCharts.chart (u f s) x‖^2 := by
  have hc (v : E) (hv : ‖v‖=1) := f.covariance s v hv
  have h := (FrameCharts.normalized_bounds (f.g s) hm (pow_pos hm _) (by
    intro v hv
    simpa only [DirectionInterpolation.empiricalCov,real_inner_comm,div_eq_mul_inv,mul_comm] using hc v hv) x).1
  change (m:ℝ)^6/(2*m)*‖x‖^2≤‖FrameCharts.chart (fun i => (Real.sqrt m)⁻¹ • f.g s i) x‖^2
  simpa only [Nat.cast_pow] using h
def B (s : Fin (m^3)) : F →L[ℝ] E :=
  ChartLinear.pseudoInverse (FrameCharts.chart (u f s)) (lower_pos hm) (energy f hm s)
lemma B_left (s : Fin (m^3)) (x : E) : B f hm s (FrameCharts.chart (u f s) x)=x := by
  have h := ChartLinear.pseudoInverse_comp (FrameCharts.chart (u f s)) (lower_pos hm) (energy f hm s)
  exact congrArg (fun L : E →L[ℝ] E => L x) h
lemma u_norm (s : Fin (m^3)) (i : Fin (m^6)) : 1/2≤‖u f s i‖ ∧ ‖u f s i‖≤2 :=
  FrameCharts.normalized_norms (f.g s) hm (f.norms s) i
lemma u_nonzero (s : Fin (m^3)) (i : Fin (m^6)) : u f s i≠0 := by
  have h := (u_norm f hm s i).1
  intro hz; rw [hz,norm_zero] at h; norm_num at h
lemma u_nonparallel (s : Fin (m^3)) (i j : Fin (m^6)) (hij : i≠j) (t : ℝ) :
    u f s i≠t • u f s j := by
  intro h
  apply f.nonparallel s i j hij t
  have hq : (Real.sqrt m)⁻¹≠0 := inv_ne_zero (ne_of_gt (Real.sqrt_pos.mpr (by exact_mod_cast hm)))
  have he := congrArg (fun x : E => Real.sqrt m • x) h
  have hq0 : Real.sqrt (m:ℝ)≠0 := ne_of_gt (Real.sqrt_pos.mpr (by exact_mod_cast hm))
  have hmul : Real.sqrt (m:ℝ)*(t*(Real.sqrt (m:ℝ))⁻¹)=t := by field_simp
  simpa only [u,smul_smul,mul_inv_cancel₀ hq0,hmul,one_smul] using he
lemma u_pivot (s : Fin (m^3)) (i : Fin (m^6)) (j : Fin m ) :
    1/((m:ℝ)^30*Real.sqrt m) < |u f s i j| := by
  have hq : 0<Real.sqrt m := Real.sqrt_pos.mpr (by exact_mod_cast hm)
  change _ < |(Real.sqrt m)⁻¹*(f.g s i j)|
  rw [abs_mul,abs_of_pos (inv_pos.mpr hq)]
  simpa only [one_div,mul_inv,mul_comm] using mul_lt_mul_of_pos_left (f.pivot s i j) (inv_pos.mpr hq)
lemma B_column (s : Fin (m^3)) (i : Fin (m^6)) :
    ‖B f hm s (EuclideanSpace.single i 1)‖≤4*((m:ℝ)/(m:ℝ)^6) := by
  have h := ChartLinear.pseudoInverse_column (FrameCharts.chart (u f s)) (lower_pos hm) (energy f hm s) (EuclideanSpace.single i 1)
  rw [FrameCharts.chart_adjoint_single] at h
  calc
    _ ≤ 2/lower m := h.trans (div_le_div_of_nonneg_right (u_norm f hm s i).2 (lower_pos hm).le)
    _ = _ := by unfold lower; field_simp; ring
lemma B_norm (s : Fin (m^3)) (x : F) : ‖B f hm s x‖≤‖x‖/Real.sqrt (lower m) :=
  ChartLinear.pseudoInverse_norm _ (lower_pos hm) (energy f hm s) x
lemma residual_norm (s : Fin (m^3)) (x : F) :
    ‖x-FrameCharts.chart (u f s) (B f hm s x)‖≤‖x‖ :=
  ChartLinear.residual_norm _ (lower_pos hm) (energy f hm s) x
end
end UniformSparsestCut.SourceCharts

namespace UniformSparsestCut.HyperplaneCount
variable {E : Type u1} {ι : Type u2} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
  [Fintype ι] [DecidableEq ι]

omit [FiniteDimensional ℝ E] [Fintype ι] in
lemma shattered_independent (f : ι → E →ₗ[ℝ] ℝ) (A : Finset (Finset ι))
    (hA : ∀ u ∈ A, ∃ x : E, ∀ i, f i x ≠ 0 ∧ (0 < f i x ↔ i ∈ u))
    {s : Finset ι} (hs : A.Shatters s) : LinearIndependent ℝ (fun i : s => f i) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  by_contra hj
  let t := s.filter (fun i => ∀ hi : i ∈ s, 0 < c ⟨i,hi⟩)
  obtain ⟨u,hu,htu⟩ := hs (t := t) (Finset.filter_subset _ _)
  obtain ⟨x,hx⟩ := hA u hu
  have hsign (i : s) : 0 < f i x ↔ 0 < c i := by
    rw [(hx i).2]
    have he : i.val ∈ s ∩ u ↔ i.val ∈ t := by rw [htu]
    simp only [Finset.mem_inter, i.property, true_and, t, Finset.mem_filter] at he
    exact he.trans ⟨fun h => h trivial, fun h _ => h⟩
  have hprod (i : s) : 0 ≤ c i * f i x := by
    by_cases hp : 0 < c i
    · exact le_of_lt (mul_pos hp ((hsign i).mpr hp))
    · exact mul_nonneg_of_nonpos_of_nonpos (le_of_not_gt hp)
        (le_of_not_gt (mt (hsign i).mp hp))
  have hpj : 0 < c j * f j x := by
    by_cases hp : 0 < c j
    · exact mul_pos hp ((hsign j).mpr hp)
    · have hn : c j < 0 := lt_of_le_of_ne (le_of_not_gt hp) hj
      have hf : f j x < 0 := lt_of_le_of_ne (le_of_not_gt (mt (hsign j).mp hp)) (hx j).1
      exact mul_pos_of_neg_of_neg hn hf
  have hp : 0 < ∑ i : s, c i * f i x :=
    Finset.sum_pos' (fun i _ => hprod i) ⟨j, Finset.mem_univ _, hpj⟩
  have hz := congrArg (fun L : E →ₗ[ℝ] ℝ => L x) hc
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, LinearMap.zero_apply] at hz
  linarith

omit [Fintype ι] in
lemma vcDim_le (f : ι → E →ₗ[ℝ] ℝ) (A : Finset (Finset ι))
    (hA : ∀ u ∈ A, ∃ x : E, ∀ i, f i x ≠ 0 ∧ (0 < f i x ↔ i ∈ u)) :
    A.vcDim ≤ Module.finrank ℝ E := by
  apply Finset.sup_le
  intro s hs
  have h := (shattered_independent f A hA (Finset.mem_shatterer.mp hs)).fintype_card_le_finrank
  simpa using h

lemma sign_patterns_bound (f : ι → E →ₗ[ℝ] ℝ) (A : Finset (Finset ι))
    (hA : ∀ u ∈ A, ∃ x : E, ∀ i, f i x ≠ 0 ∧ (0 < f i x ↔ i ∈ u)) :
    A.card ≤ ∑ k ∈ Finset.Iic (Module.finrank ℝ E), (Fintype.card ι).choose k := by
  have hv := vcDim_le f A hA
  exact (Finset.card_le_card_shatterer A).trans
    (Finset.card_shatterer_le_sum_vcDim.trans
      (Finset.sum_le_sum_of_subset (Finset.Iic_subset_Iic.mpr hv)))

end UniformSparsestCut.HyperplaneCount

namespace UniformSparsestCut.RoundedCharts
open MeasureTheory Set Filter
open scoped Topology BigOperators RealInnerProductSpace
variable {m N S : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "F" => EuclideanSpace ℝ (Fin N)

def cube (R : ℝ) : Set E := {θ | ∀ j, |θ j| < R}

def regular (u : Fin N → E) (τ : ℝ) (θ : E) : Prop :=
  ∀ i (k : ℤ), inner ℝ (u i) θ ≠ (k:ℝ)*τ

def integerLabel (u : Fin N → E) (τ : ℝ) (θ : E) (i : Fin N) : ℤ :=
  ⌊inner ℝ (u i) θ/τ⌋

def rounded (u : Fin N → E) (τ : ℝ) (θ : E) : F :=
  WithLp.toLp 2 (fun i => τ*(integerLabel u τ θ i : ℝ))

def Vertex (u : Fin S → Fin N → E) (τ : ℝ) :=
  {p : Fin S × (Fin N → ℤ) // ∃ θ ∈ cube 2, regular (u p.1) τ θ ∧ integerLabel (u p.1) τ θ = p.2}

def coordinate (u : Fin S → Fin N → E) (τ : ℝ) (v : Vertex u τ) : F :=
  WithLp.toLp 2 (fun i => τ*(v.val.2 i : ℝ))

lemma cube_norm {R : ℝ} (hR : 0 ≤ R) {θ : E} (hθ : θ ∈ cube R) :
    ‖θ‖ ≤ R*Real.sqrt m := by
  have hs : ‖θ‖^2 ≤ (m:ℝ)*R^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc
      _ ≤ ∑ _j : Fin m, R^2 := by
        apply Finset.sum_le_sum; intro j _
        rw [Real.norm_eq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hθ j).le _
      _ = _ := by simp
  have hroot := Real.sq_sqrt (Nat.cast_nonneg m)
  have hp : 0 ≤ R*Real.sqrt m := mul_nonneg hR (Real.sqrt_nonneg _)
  have he : (R*Real.sqrt m)^2 = (m:ℝ)*R^2 := by rw [mul_pow,hroot]; ring
  nlinarith [norm_nonneg θ]

lemma hyperplane_null (u : E) (hu : u ≠ 0) (t : ℝ) :
    volume {x : E | inner ℝ u x = t} = 0 := by
  let H : AffineSubspace ℝ E :=
    { carrier := {x | inner ℝ u x = t}
      smul_vsub_vadd_mem' := by
        intro c x y z hx hy hz
        change inner ℝ u x = t at hx
        change inner ℝ u y = t at hy
        change inner ℝ u z = t at hz
        change inner ℝ u (c • (x-y)+z) = t
        simp only [inner_add_right, inner_smul_right, inner_sub_right, hx, hy, hz]
        ring }
  have ht : H ≠ ⊤ := by
    intro he
    have hzero : (0:E) ∈ H := by rw [he]; trivial
    have hone : u ∈ H := by rw [he]; trivial
    change inner ℝ u 0 = t at hzero
    change inner ℝ u u = t at hone
    rw [inner_zero_right] at hzero
    have := ((inner_self_eq_zero (𝕜 := ℝ)).mp (hone.trans hzero.symm))
    exact hu this
  exact Measure.addHaar_affineSubspace volume H ht

lemma ae_regular (u : Fin N → E) (τ : ℝ) (hu : ∀ i, u i ≠ 0) :
    ∀ᵐ θ : E, regular u τ θ := by
  have hi (i : Fin N) (k : ℤ) : ∀ᵐ θ : E, inner ℝ (u i) θ ≠ (k:ℝ)*τ := by
    rw [ae_iff]
    simpa only [not_not] using hyperplane_null (u i) (hu i) ((k:ℝ)*τ)
  have hi' (i : Fin N) : ∀ᵐ θ : E, ∀ k : ℤ, inner ℝ (u i) θ ≠ (k:ℝ)*τ :=
    ae_all_iff.mpr (hi i)
  exact ae_all_iff.mpr hi'

lemma rounded_error_coordinate (u : Fin N → E) {τ : ℝ} (hτ : 0 < τ) (θ : E) (i : Fin N) :
    0 ≤ inner ℝ (u i) θ-rounded u τ θ i ∧ inner ℝ (u i) θ-rounded u τ θ i < τ := by
  have hlo := Int.floor_le (inner ℝ (u i) θ/τ)
  have hhi := Int.lt_floor_add_one (inner ℝ (u i) θ/τ)
  have hl := (le_div_iff₀ hτ).mp hlo
  have hh := (div_lt_iff₀ hτ).mp hhi
  change 0 ≤ inner ℝ (u i) θ-τ*(⌊inner ℝ (u i) θ/τ⌋:ℝ) ∧
    inner ℝ (u i) θ-τ*(⌊inner ℝ (u i) θ/τ⌋:ℝ) < τ
  constructor <;> nlinarith

lemma rounded_error (u : Fin N → E) {τ : ℝ} (hτ : 0 < τ) (θ : E) :
    ‖rounded u τ θ - FrameCharts.chart u θ‖ ≤ Real.sqrt N*τ := by
  have hs : ‖rounded u τ θ - FrameCharts.chart u θ‖^2 ≤ (N:ℝ)*τ^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc
      _ ≤ ∑ _i : Fin N, τ^2 := by
        apply Finset.sum_le_sum; intro i _
        simp only [PiLp.sub_apply, FrameCharts.chart_apply, Real.norm_eq_abs, sq_abs]
        have hh := rounded_error_coordinate u hτ θ i
        nlinarith
      _ = _ := by simp
  have hr := Real.sq_sqrt (Nat.cast_nonneg N)
  have hp : 0 ≤ Real.sqrt N*τ := mul_nonneg (Real.sqrt_nonneg _) hτ.le
  have he : (Real.sqrt N*τ)^2 = (N:ℝ)*τ^2 := by rw [mul_pow,hr]
  nlinarith [norm_nonneg (rounded u τ θ-FrameCharts.chart u θ)]

lemma integerLabel_bound (u : Fin N → E) {τ : ℝ} (hτ : 0 < τ) (hu : ∀ i, ‖u i‖ ≤ 2)
    {θ : E} (hθ : θ ∈ cube 2) (i : Fin N) :
    |(integerLabel u τ θ i : ℝ)| ≤ 4*Real.sqrt m/τ+1 := by
  have hn := cube_norm (by norm_num : (0:ℝ) ≤ 2) hθ
  have hh : |inner ℝ (u i) θ| ≤ 4*Real.sqrt m := by
    calc
      _ ≤ ‖u i‖*‖θ‖ := abs_real_inner_le_norm _ _
      _ ≤ 2*(2*Real.sqrt m) := mul_le_mul (hu i) hn (norm_nonneg θ) (by norm_num)
      _ = _ := by ring
  have hf := Int.floor_le (inner ℝ (u i) θ/τ)
  have hfl := Int.lt_floor_add_one (inner ℝ (u i) θ/τ)
  have hab : |inner ℝ (u i) θ/τ| ≤ 4*Real.sqrt m/τ := by
    rw [abs_div, abs_of_pos hτ]
    exact div_le_div_of_nonneg_right hh hτ.le
  change |(⌊inner ℝ (u i) θ/τ⌋:ℝ)| ≤ _
  rw [abs_le] at hab ⊢
  constructor <;> linarith

lemma vertex_finite (u : Fin S → Fin N → E) {τ : ℝ} (hτ : 0 < τ)
    (hu : ∀ s i, ‖u s i‖ ≤ 2) : Finite (Vertex u τ) := by
  let B : ℤ := ⌈4*Real.sqrt m/τ+1⌉
  let f : Vertex u τ → Fin S × (Fin N → ↥(Finset.Icc (-B) B)) := fun v =>
    (v.val.1, fun i => ⟨v.val.2 i, by
      obtain ⟨θ,hθ,hr,hlabel⟩ := v.property
      have hb := integerLabel_bound (u v.val.1) hτ (hu v.val.1) hθ i
      have hB := Int.le_ceil (4*Real.sqrt m/τ+1)
      have hv : |(v.val.2 i:ℝ)| ≤ (B:ℝ) := by rw [← hlabel]; exact hb.trans hB
      have hlo : -B ≤ v.val.2 i := by exact_mod_cast (abs_le.mp hv).1
      have hhi : v.val.2 i ≤ B := by exact_mod_cast (abs_le.mp hv).2
      exact Finset.mem_Icc.mpr ⟨hlo,hhi⟩⟩)
  apply Finite.of_injective f
  intro v w h
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun z : Fin S × (Fin N → ↥(Finset.Icc (-B) B)) => z.1) h
  · funext i
    exact congrArg (fun z : Fin S × (Fin N → ↥(Finset.Icc (-B) B)) => (z.2 i).val) h

lemma representative (u : Fin S → Fin N → E) (τ : ℝ) (v : Vertex u τ) :
    ∃ θ ∈ cube 2, regular (u v.val.1) τ θ ∧ coordinate u τ v = rounded (u v.val.1) τ θ := by
  obtain ⟨θ,hθ,hr,hl⟩ := v.property
  refine ⟨θ,hθ,hr,?_⟩
  ext i
  change τ*(v.val.2 i : ℝ) = τ*(integerLabel (u v.val.1) τ θ i : ℝ)
  rw [hl]

end UniformSparsestCut.RoundedCharts

namespace UniformSparsestCut.SourceCharts
open scoped BigOperators RealInnerProductSpace
noncomputable section
variable {m : ℕ} (f : PivotFamily.PFamily m) (hm : 0 < m)
local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "F" => EuclideanSpace ℝ (Fin (m^6))
lemma lower_ge_one (hm2 : 2 ≤ m) : 1≤lower m := by
  have hx : (2:ℝ) ≤ m := by exact_mod_cast hm2
  have hp := pow_le_pow_right₀ (by linarith : (1:ℝ) ≤ m) (show 2≤6 by norm_num)
  unfold lower
  apply (le_div_iff₀ (by positivity : (0:ℝ)<2*m)).mpr
  nlinarith
lemma B_norm_le (hm2 : 2 ≤ m) (s : Fin (m^3)) (x : F) : ‖B f hm s x‖≤‖x‖ := by
  exact (B_norm f hm s x).trans (div_le_self (norm_nonneg _) ((Real.one_le_sqrt).mpr (lower_ge_one hm2)))
lemma rounded_B_error (hm2 : 2 ≤ m) {τ : ℝ} (hτ : 0<τ) (s : Fin (m^3)) (θ : E) :
    ‖B f hm s (RoundedCharts.rounded (u f s) τ θ)-θ‖≤Real.sqrt (m^6:ℕ)*τ := by
  have he : B f hm s (RoundedCharts.rounded (u f s) τ θ)-θ=
      B f hm s (RoundedCharts.rounded (u f s) τ θ-FrameCharts.chart (u f s) θ) := by
    rw [map_sub,B_left]
  rw [he]
  exact (B_norm_le f hm hm2 s _).trans (RoundedCharts.rounded_error _ hτ θ)
lemma rounded_residual_error {τ : ℝ} (hτ : 0<τ) (s : Fin (m^3)) (θ : E) :
    ‖RoundedCharts.rounded (u f s) τ θ-FrameCharts.chart (u f s) (B f hm s (RoundedCharts.rounded (u f s) τ θ))‖≤
      Real.sqrt (m^6:ℕ)*τ := by
  let x := RoundedCharts.rounded (u f s) τ θ
  have he : x-FrameCharts.chart (u f s) (B f hm s x)=
      (x-FrameCharts.chart (u f s) θ)-FrameCharts.chart (u f s) (B f hm s (x-FrameCharts.chart (u f s) θ)) := by
    rw [map_sub,B_left,map_sub]
    abel
  change ‖x-FrameCharts.chart (u f s) (B f hm s x)‖≤_
  rw [he]
  exact (residual_norm f hm s _).trans (RoundedCharts.rounded_error _ hτ θ)
lemma vertex_B_bound (hm2 : 2 ≤ m) {τ : ℝ} (hτ : 0<τ) (v : RoundedCharts.Vertex (u f) τ) :
    ‖B f hm v.val.1 (RoundedCharts.coordinate (u f) τ v)‖≤2*Real.sqrt m+Real.sqrt (m^6:ℕ)*τ := by
  obtain ⟨θ,hθ,hr,hx⟩ := RoundedCharts.representative (u f) τ v
  rw [hx]
  have h := rounded_B_error f hm hm2 hτ v.val.1 θ
  have ht := RoundedCharts.cube_norm (by norm_num : (0:ℝ)≤2) hθ
  exact (norm_le_norm_sub_add _ θ).trans (by linarith)
lemma vertex_residual_bound {τ : ℝ} (hτ : 0<τ) (v : RoundedCharts.Vertex (u f) τ) :
    ‖RoundedCharts.coordinate (u f) τ v-FrameCharts.chart (u f v.val.1) (B f hm v.val.1 (RoundedCharts.coordinate (u f) τ v))‖≤
      Real.sqrt (m^6:ℕ)*τ := by
  obtain ⟨θ,hθ,hr,hx⟩ := RoundedCharts.representative (u f) τ v
  rw [hx]
  exact rounded_residual_error f hm hτ v.val.1 θ
end
end UniformSparsestCut.SourceCharts

end

end OAI
