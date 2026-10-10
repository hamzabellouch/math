import OAI.Dynamics.EntropyCounterexample.Embedding

namespace OAI

noncomputable section

open scoped ContDiff

namespace Problem340.AmbientRetraction

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def normalize (x : E) : E := ‖x‖⁻¹ • x

theorem contDiffAt_normalize {n : ℕ∞ω} {x : E} (hx : x ≠ 0) :
    ContDiffAt ℝ n normalize x := by
  exact ((contDiffAt_id.norm ℝ hx).inv (norm_ne_zero_iff.mpr hx)).smul contDiffAt_id

theorem normalize_mem_sphere {x : E} (hx : x ≠ 0) :
    normalize x ∈ Metric.sphere (0 : E) 1 := by
  rw [mem_sphere_zero_iff_norm, normalize, norm_smul, norm_inv, norm_norm]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)

theorem normalize_eq_self {x : E} (hx : x ∈ Metric.sphere (0 : E) 1) :
    normalize x = x := by
  rw [normalize, mem_sphere_zero_iff_norm.mp hx, inv_one, one_smul]

@[simp]
theorem norm_smul_normalize (x : E) : ‖x‖ • normalize x = x := by
  by_cases hx : x = 0
  · simp [hx, normalize]
  · rw [normalize, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx), one_smul]

theorem norm_normalize_le_one (x : E) : ‖normalize x‖ ≤ 1 := by
  by_cases hx : x = 0
  · simp [hx, normalize]
  · exact le_of_eq (mem_sphere_zero_iff_norm.mp (normalize_mem_sphere hx))

theorem norm_normalize_sub_le {x : E} (hx : x ≠ 0) (y : E) :
    ‖normalize y - normalize x‖ ≤ (2 / ‖x‖) * ‖y - x‖ := by
  have hid : ‖x‖ • (normalize y - normalize x) =
      (‖x‖ - ‖y‖) • normalize y + (y - x) := by
    rw [smul_sub, sub_smul, norm_smul_normalize, norm_smul_normalize]
    abel
  have hscale : ‖x‖ * ‖normalize y - normalize x‖ ≤ 2 * ‖y - x‖ := by
    calc
      ‖x‖ * ‖normalize y - normalize x‖ =
          ‖‖x‖ • (normalize y - normalize x)‖ := by rw [norm_smul, norm_norm]
      _ = ‖(‖x‖ - ‖y‖) • normalize y + (y - x)‖ := congrArg norm hid
      _ ≤ ‖(‖x‖ - ‖y‖) • normalize y‖ + ‖y - x‖ := norm_add_le _ _
      _ = |‖x‖ - ‖y‖| * ‖normalize y‖ + ‖y - x‖ := by
        rw [norm_smul, Real.norm_eq_abs]
      _ ≤ |‖x‖ - ‖y‖| + ‖y - x‖ := by
        nlinarith [norm_normalize_le_one y, abs_nonneg (‖x‖ - ‖y‖)]
      _ ≤ 2 * ‖y - x‖ := by
        have hnorm := abs_norm_sub_norm_le x y
        rw [norm_sub_rev x y] at hnorm
        linarith
  calc
    ‖normalize y - normalize x‖ ≤ (2 * ‖y - x‖) / ‖x‖ :=
      (le_div_iff₀ (norm_pos_iff.mpr hx)).mpr (by nlinarith [hscale])
    _ = (2 / ‖x‖) * ‖y - x‖ := by ring

theorem norm_fderiv_normalize_le {x : E} (hx : x ≠ 0) :
    ‖fderiv ℝ normalize x‖ ≤ 2 / ‖x‖ := by
  apply norm_fderiv_le_of_lip' ℝ (by positivity)
  exact Filter.Eventually.of_forall (norm_normalize_sub_le hx)

theorem norm_fderiv_normalize_le_four {x : E} (hx : (1 / 2 : ℝ) ≤ ‖x‖) :
    ‖fderiv ℝ normalize x‖ ≤ 4 := by
  have hxpos : 0 < ‖x‖ := by linarith
  apply (norm_fderiv_normalize_le (norm_pos_iff.mp hxpos)).trans
  apply (div_le_iff₀ hxpos).mpr
  linarith

def cylinder (x : ℝ × E) : ℝ × E := (x.1, normalize x.2)

theorem contDiffAt_cylinder {n : ℕ∞ω} {x : ℝ × E} (hx : x.2 ≠ 0) :
    ContDiffAt ℝ n cylinder x := by
  exact contDiffAt_fst.prodMk ((contDiffAt_normalize hx).comp x contDiffAt_snd)

theorem norm_cylinder_sub_le_four {x : ℝ × E} (hx : (1 / 2 : ℝ) ≤ ‖x.2‖)
    (y : ℝ × E) : ‖cylinder y - cylinder x‖ ≤ 4 * ‖y - x‖ := by
  have hxpos : 0 < ‖x.2‖ := by linarith
  have hratio : 2 / ‖x.2‖ ≤ 4 := (div_le_iff₀ hxpos).mpr (by linarith)
  change max ‖y.1 - x.1‖ ‖normalize y.2 - normalize x.2‖ ≤ 4 * ‖y - x‖
  apply max_le
  · have hfst := norm_fst_le (y - x)
    change ‖y.1 - x.1‖ ≤ ‖y - x‖ at hfst
    nlinarith [norm_nonneg (y - x)]
  · calc
      ‖normalize y.2 - normalize x.2‖ ≤ (2 / ‖x.2‖) * ‖y.2 - x.2‖ :=
        norm_normalize_sub_le (norm_pos_iff.mp hxpos) _
      _ ≤ 4 * ‖y.2 - x.2‖ := mul_le_mul_of_nonneg_right hratio (norm_nonneg _)
      _ ≤ 4 * ‖y - x‖ := mul_le_mul_of_nonneg_left (norm_snd_le (y - x)) (by norm_num)

theorem norm_fderiv_cylinder_le_four {x : ℝ × E} (hx : (1 / 2 : ℝ) ≤ ‖x.2‖) :
    ‖fderiv ℝ cylinder x‖ ≤ 4 := by
  apply norm_fderiv_le_of_lip' ℝ (by norm_num)
  exact Filter.Eventually.of_forall (norm_cylinder_sub_le_four hx)

@[simp]
theorem cylinder_eq_self {x : ℝ × E} (hx : ‖x.2‖ = 1) : cylinder x = x := by
  apply Prod.ext
  · rfl
  · exact normalize_eq_self (mem_sphere_zero_iff_norm.mpr hx)

def cylinderDomain : Set (ℝ × E) := {x | (1 / 2 : ℝ) < ‖x.2‖}

omit [InnerProductSpace ℝ E] in
theorem isOpen_cylinderDomain : IsOpen (cylinderDomain (E := E)) :=
  isOpen_lt continuous_const (continuous_norm.comp continuous_snd)

theorem mapsTo_normalizedPredictor
    (G : ℝ × E → ℝ × E)
    (hG : ∀ x : ℝ × E, ‖x.2‖ = 1 → ‖(G x).2‖ = 1) :
    Set.MapsTo (G ∘ cylinder) cylinderDomain cylinderDomain := by
  intro x hx
  change (1 / 2 : ℝ) < ‖x.2‖ at hx
  have hxne : x.2 ≠ 0 := norm_pos_iff.mp (by linarith [hx])
  have hn : ‖(cylinder x).2‖ = 1 :=
    mem_sphere_zero_iff_norm.mp (normalize_mem_sphere hxne)
  change (1 / 2 : ℝ) < ‖(G (cylinder x)).2‖
  rw [hG _ hn]
  norm_num

theorem contDiffOn_normalizedPredictor {n : ℕ∞ω}
    (G : ℝ × E → ℝ × E) (hG : ContDiff ℝ n G) :
    ContDiffOn ℝ n (G ∘ cylinder) cylinderDomain := by
  intro x hx
  change (1 / 2 : ℝ) < ‖x.2‖ at hx
  apply ContDiffAt.contDiffWithinAt
  exact hG.contDiffAt.comp x (contDiffAt_cylinder
    (norm_pos_iff.mp (by linarith [hx])))

theorem norm_fderiv_normalizedPredictor_le
    (G : ℝ × E → ℝ × E) (hG : ContDiff ℝ 1 G)
    {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ x : ℝ × E, ‖x.2‖ = 1 → ‖fderiv ℝ G x‖ ≤ B)
    {x : ℝ × E} (hx : x ∈ cylinderDomain) :
    ‖fderiv ℝ (G ∘ cylinder) x‖ ≤ B * 4 := by
  change (1 / 2 : ℝ) < ‖x.2‖ at hx
  have hxpos : 0 < ‖x.2‖ := by linarith [hx]
  have hnorm : ‖(cylinder x).2‖ = 1 :=
    mem_sphere_zero_iff_norm.mp (normalize_mem_sphere (norm_pos_iff.mp hxpos))
  rw [fderiv_comp x (hG.differentiable one_ne_zero _)
    ((contDiffAt_cylinder (n := 1) (norm_pos_iff.mp hxpos)).differentiableAt one_ne_zero)]
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  exact mul_le_mul (hbound _ hnorm) (norm_fderiv_cylinder_le_four (le_of_lt hx))
    (norm_nonneg _) hB

theorem normalizedPredictor_iterate_eq
    (G : ℝ × E → ℝ × E)
    (hG : ∀ x : ℝ × E, ‖x.2‖ = 1 → ‖(G x).2‖ = 1)
    {x : ℝ × E} (hx : ‖x.2‖ = 1) (n : ℕ) :
    (G ∘ cylinder)^[n] x = G^[n] x := by
  have hinv : Set.MapsTo G {x : ℝ × E | ‖x.2‖ = 1} {x : ℝ × E | ‖x.2‖ = 1} := hG
  induction n with
  | zero => rfl
  | succ n hn =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hn]
      change G (cylinder (G^[n] x)) = G (G^[n] x)
      rw [cylinder_eq_self (hinv.iterate n hx)]

theorem normalizedPredictor_iterate_succ_eq
    (G : ℝ × E → ℝ × E)
    (hG : ∀ x : ℝ × E, ‖x.2‖ = 1 → ‖(G x).2‖ = 1)
    {x : ℝ × E} (hx : x.2 ≠ 0) (n : ℕ) :
    (G ∘ cylinder)^[n + 1] x = G^[n + 1] (cylinder x) := by
  rw [Function.iterate_succ_apply, Function.comp_apply]
  have hn : ‖(G (cylinder x)).2‖ = 1 :=
    hG _ (mem_sphere_zero_iff_norm.mp (normalize_mem_sphere hx))
  rw [normalizedPredictor_iterate_eq G hG hn n, Function.iterate_succ_apply]

def domain (q : ℕ) : Set (CounterexampleAmbient q) :=
  {x | x.1 ≠ 0 ∧ ∀ i, x.2 i ≠ 0}

theorem isOpen_domain (q : ℕ) : IsOpen (domain q) := by
  have hclock : IsOpen {x : CounterexampleAmbient q | x.1 ≠ 0} :=
    isOpen_ne.preimage continuous_fst
  have hsphere : IsOpen {x : CounterexampleAmbient q | ∀ i, x.2 i ≠ 0} := by
    rw [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun i =>
      isOpen_ne.preimage ((continuous_apply i).comp continuous_snd)
  exact hclock.inter hsphere

theorem standardEmbedding_mem_domain {q : ℕ} (x : CounterexampleManifold q) :
    standardEmbedding q x ∈ domain q :=
  ⟨ne_zero_of_mem_unit_sphere x.1, fun i => ne_zero_of_mem_unit_sphere (x.2 i)⟩

def project (q : ℕ) (x : CounterexampleAmbient q) : CounterexampleAmbient q :=
  (normalize x.1, fun i => normalize (x.2 i))

theorem contDiffOn_project (q : ℕ) (n : ℕ∞ω) :
    ContDiffOn ℝ n (project q) (domain q) := by
  intro x hx
  apply ContDiffAt.contDiffWithinAt
  apply ContDiffAt.prodMk
  · exact (contDiffAt_normalize (E := ClockAmbient) (n := n) hx.1).comp x contDiffAt_fst
  · apply (contDiffAt_pi (F' := fun _ : Fin (q + 1) => SphereAmbient)).mpr
    intro i
    exact ContDiffAt.comp (f := fun y : CounterexampleAmbient q => y.2 i)
      (g := normalize (E := SphereAmbient)) x
      (contDiffAt_normalize (n := n) (hx.2 i))
      ((contDiff_apply ℝ SphereAmbient i).contDiffAt.comp x contDiffAt_snd)

@[simp]
theorem project_standardEmbedding {q : ℕ} (x : CounterexampleManifold q) :
    project q (standardEmbedding q x) = standardEmbedding q x := by
  apply Prod.ext
  · exact normalize_eq_self x.1.property
  · funext i
    exact normalize_eq_self (x.2 i).property

def toManifold (q : ℕ) (x : domain q) : CounterexampleManifold q :=
  (⟨normalize x.1.1, normalize_mem_sphere x.2.1⟩,
    fun i => ⟨normalize (x.1.2 i), normalize_mem_sphere (x.2.2 i)⟩)

@[simp]
theorem standardEmbedding_toManifold (q : ℕ) (x : domain q) :
    standardEmbedding q (toManifold q x) = project q x := rfl

theorem continuous_toManifold (q : ℕ) : Continuous (toManifold q) := by
  apply (continuous_iff_standardEmbedding q _).mpr
  exact (contDiffOn_project q 0).continuousOn.domRestrict

@[simp]
theorem toManifold_standardEmbedding {q : ℕ} (x : CounterexampleManifold q) :
    toManifold q ⟨standardEmbedding q x, standardEmbedding_mem_domain x⟩ = x := by
  apply standardEmbedding_injective q
  exact project_standardEmbedding x

def fromAmbient {q : ℕ} (F : CounterexampleAmbient q → CounterexampleAmbient q)
    (hF : ∀ x : CounterexampleManifold q, F (standardEmbedding q x) ∈ domain q)
    (x : CounterexampleManifold q) : CounterexampleManifold q :=
  toManifold q ⟨F (standardEmbedding q x), hF x⟩

@[simp]
theorem standardEmbedding_fromAmbient {q : ℕ}
    (F : CounterexampleAmbient q → CounterexampleAmbient q)
    (hF : ∀ x : CounterexampleManifold q, F (standardEmbedding q x) ∈ domain q)
    (x : CounterexampleManifold q) :
    standardEmbedding q (fromAmbient F hF x) =
      project q (F (standardEmbedding q x)) := rfl

theorem isC1SelfMap_fromAmbient {q : ℕ}
    (F : CounterexampleAmbient q → CounterexampleAmbient q)
    (hF : ∀ x : CounterexampleManifold q, F (standardEmbedding q x) ∈ domain q)
    {U : Set (CounterexampleAmbient q)} (hU : IsOpen U)
    (hmem : ∀ x : CounterexampleManifold q, standardEmbedding q x ∈ U)
    (hsmooth : ContDiffOn ℝ 1 F U) : IsC1SelfMap q (fromAmbient F hF) := by
  have hlocal : ∀ x : CounterexampleManifold q,
      ∃ V : Set (CounterexampleAmbient q),
        IsOpen V ∧ standardEmbedding q x ∈ V ∧
          ∃ G : CounterexampleAmbient q → CounterexampleAmbient q,
            ContDiffOn ℝ 1 G V ∧
              ∀ y : CounterexampleManifold q,
                standardEmbedding q y ∈ V →
                  standardEmbedding q (fromAmbient F hF y) = G (standardEmbedding q y) := by
    intro x
    refine ⟨U ∩ F ⁻¹' domain q,
      hsmooth.continuousOn.isOpen_inter_preimage hU (isOpen_domain q),
      ⟨hmem x, hF x⟩, project q ∘ F, ?_, ?_⟩
    · exact (contDiffOn_project q 1).comp_inter hsmooth
    · intro y _
      rfl
  exact ⟨continuous_of_local_contDiff_extension _ hlocal, hlocal⟩

end Problem340.AmbientRetraction

end

end OAI
