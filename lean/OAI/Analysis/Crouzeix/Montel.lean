import Mathlib

namespace OAI

/-! Montel. -/

noncomputable section

open Set Filter Metric Topology Function

namespace CrouzeixHilbert.Conformal

theorem norm_deriv_le_on_half_ball {f : ℂ → ℂ} {U : Set ℂ}
    (_hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hb : ∀ z ∈ U, ‖f z‖ ≤ 1) {x : ℂ} {R : ℝ} (hR : 0 < R)
    (hRU : ball x R ⊆ U) {y : ℂ} (hy : y ∈ ball x (R / 2)) :
    ‖deriv f y‖ ≤ 1 / (R / 2) := by
  have hsub : closedBall y (R / 2) ⊆ U := by
    intro z hz
    apply hRU
    have hy' : dist y x < R / 2 := hy
    have hz' : dist z y ≤ R / 2 := hz
    exact (dist_triangle z y x).trans_lt (by linarith)
  apply Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by positivity)
  · exact (hf.mono (by simpa [closure_ball _ (by positivity : R / 2 ≠ 0)] using hsub)).diffContOnCl
  · exact fun z hz => hb z (hsub (sphere_subset_closedBall hz))

theorem equicontinuous_restrict_of_holomorphic_bounded {ι : Type*}
    {F : ι → ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hd : ∀ i, DifferentiableOn ℂ (F i) U)
    (hb : ∀ i z, z ∈ U → ‖F i z‖ ≤ 1) :
    Equicontinuous (fun i (z : U) => F i z) := by
  intro x
  obtain ⟨R, hR, hRU⟩ := Metric.isOpen_iff.mp hU x x.2
  have hR2 : 0 < R / 2 := by positivity
  let C : ℝ := 1 / (R / 2)
  have hC : 0 < C := by dsimp [C]; positivity
  rw [Metric.equicontinuousAt_iff]
  intro ε hε
  refine ⟨min (R / 2) (ε / C), lt_min hR2 (div_pos hε hC), ?_⟩
  intro y hy i
  have hyR : (y : ℂ) ∈ ball (x : ℂ) (R / 2) := lt_of_lt_of_le hy (min_le_left _ _)
  have hbound : ‖F i y - F i x‖ ≤ C * ‖(y : ℂ) - x‖ := by
    apply (convex_ball (x : ℂ) (R / 2)).norm_image_sub_le_of_norm_deriv_le
    · intro z hz
      exact (hd i).differentiableAt (hU.mem_nhds (hRU (Metric.ball_subset_ball (by linarith) hz)))
    · intro z hz
      exact norm_deriv_le_on_half_ball hU (hd i) (hb i) hR hRU hz
    · exact mem_ball_self hR2
    · exact hyR
  rw [dist_comm, dist_eq_norm]
  apply hbound.trans_lt
  apply (lt_div_iff₀' hC).1
  simpa [Subtype.dist_eq, dist_eq_norm] using (lt_of_lt_of_le hy (min_le_right _ _) : dist y x < ε / C)

def extend (U : Set ℂ) (f : U → ℂ) (z : ℂ) : ℂ := by
  classical
  exact if h : z ∈ U then f ⟨z, h⟩ else 0

@[simp] theorem extend_apply {U : Set ℂ} (f : U → ℂ) (z : U) :
    extend U f z = f z := by simp [extend, z.2]

theorem montel {U : Set ℂ} (hU : IsOpen U) (F : ℕ → ℂ → ℂ)
    (hd : ∀ n, DifferentiableOn ℂ (F n) U)
    (hb : ∀ n z, z ∈ U → ‖F n z‖ ≤ 1) :
    ∃ (f : ℂ → ℂ) (φ : ℕ → ℕ), StrictMono φ ∧
      TendstoLocallyUniformlyOn (F ∘ φ) f atTop U ∧
      DifferentiableOn ℂ f U ∧ ∀ z ∈ U, ‖f z‖ ≤ 1 := by
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  let : T2Space (UniformOnFun U ℂ {K | IsCompact K}) :=
    UniformOnFun.t2Space_of_covering (Set.eq_univ_iff_forall.mpr (fun x =>
      mem_sUnion_of_mem (mem_singleton x) isCompact_singleton))
  let S : Set C(U, ℂ) := {f | DifferentiableOn ℂ (extend U f) U ∧ ∀ z, ‖f z‖ ≤ 1}
  have heq : Equicontinuous (fun (f : S) (z : U) => (f : C(U, ℂ)) z) := by
    simpa using equicontinuous_restrict_of_holomorphic_bounded hU
      (fun (f : S) => f.2.1) (fun (f : S) z hz => by
        simpa [extend, hz] using f.2.2 ⟨z, hz⟩)
  have hc : IsCompact (closure S) := by
    apply ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
      (F := fun (f : C(U, ℂ)) => (f : U → ℂ)) (𝔖 := {K | IsCompact K})
      (fun _ hK => hK)
      ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isClosedEmbedding
    · exact fun K _ => heq.equicontinuousOn K
    · intro K _ x _
      exact ⟨closedBall 0 1, isCompact_closedBall 0 1, fun f hf => by
        simpa using hf.2 x⟩
  let G : ℕ → C(U, ℂ) := fun n => ⟨fun z => F n z, (hd n).continuousOn.domRestrict⟩
  have hGS : ∀ n, G n ∈ S := by
    intro n
    constructor
    · apply (hd n).congr
      intro z hz
      exact extend_apply (G n) ⟨z, hz⟩
    · exact fun z => hb n z z.2
  obtain ⟨g, _, φ, hφ, hlim⟩ := hc.tendsto_subseq (fun n => subset_closure (hGS n))
  have hconv : TendstoLocallyUniformlyOn (F ∘ φ) (extend U g) atTop U := by
    rw [tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe]
    have hl := ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp hlim
    change TendstoLocallyUniformly (fun i (z : U) => F (φ i) z) g atTop at hl
    convert hl using 1
    · funext i z
      rfl
    · funext z
      exact extend_apply g z
  refine ⟨extend U g, φ, hφ, hconv, hconv.differentiableOn
    (Eventually.of_forall (fun n => hd (φ n))) hU, ?_⟩
  intro z hz
  exact le_of_tendsto' (hconv.tendsto_at hz).norm (fun n => hb (φ n) z hz)

end CrouzeixHilbert.Conformal

end

end OAI
