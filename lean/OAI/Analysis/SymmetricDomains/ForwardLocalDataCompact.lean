import Mathlib
import OAI.Analysis.SymmetricDomains.ScalingExpanding

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Metric
open scoped Topology

theorem bounded_cocompact_expanding_limit_mem {d n : ℕ} {Γ : Type*}
    (D : Set (Affine d)) (hD : IsOpen D) (hconn : IsPreconnected D)
    (U : Set (Affine n)) [LocallyCompactSpace U]
    (hbounded : Bornology.IsBounded U)
    [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ] [MulAction Γ U] [ProperSMul Γ U]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))
    (K : Set U) (hK : IsCompact K) (hrep : ∀ x : U, ∃ k ∈ K, ∃ γ : Γ, γ • k = x)
    (g : ℕ → Affine d → Affine n) (G : Affine d → Affine n) (x₀ : D)
    (hbase : ∃ C : Set U, IsCompact C ∧ ∀ᶠ j in atTop, g j x₀.val ∈ Subtype.val '' C)
    (hlocal : ∀ x ∈ D, ∃ W : Set (Affine d), IsOpen W ∧ x ∈ W ∧ W ⊆ D ∧
      ∀ᶠ j in atTop, AnalyticOnNhd ℂ (g j) W ∧ MapsTo (g j) W U)
    (hconv : ∀ x ∈ D, Tendsto (fun j => g j x) atTop (𝓝 (G x))) :
    MapsTo G D U := by
  classical
  obtain ⟨C,hC,hbaseC⟩ := hbase
  obtain ⟨j,hj⟩ := hbaseC.exists
  obtain ⟨u₀,_,_⟩ := hj
  let F : ℕ → D → U := fun j x => if hx : g j x.val ∈ U then ⟨g j x.val,hx⟩ else u₀
  have hFval {j : ℕ} {x : D} (hx : g j x.val ∈ U) : (F j x).val = g j x.val := by
    simp only [F,dite_eq_left hx]
  have hFbase : ∃ C' : Set U, IsCompact C' ∧ ∀ᶠ j in atTop, F j x₀ ∈ C' := by
    refine ⟨C,hC,?_⟩
    filter_upwards [hbaseC] with j hj
    obtain ⟨u,hu,he⟩ := hj
    have huval : g j x₀.val ∈ U := he ▸ u.property
    have hFhu : F j x₀ = u := Subtype.ext ((hFval huval).trans he.symm)
    exact hFhu ▸ hu
  have hFhol : LocallyEventuallyHolomorphic D U F atTop := by
    intro x
    obtain ⟨W,hWo,hxW,hWD,he⟩ := hlocal x.val x.property
    refine ⟨W,hWo,hxW,hWD,?_⟩
    filter_upwards [he] with j hj
    intro p
    refine ⟨W,hWo,p.property,g j,hj.1,?_⟩
    intro q _
    exact (hFval (x := ⟨q.val,hWD q.property⟩) (hj.2 q.property)).symm
  have hFconv : ∀ x : D, Tendsto (fun j => (F j x).val) atTop (𝓝 (G x.val)) := by
    intro x
    obtain ⟨W,_,hxW,_,he⟩ := hlocal x.val x.property
    apply (hconv x.val x.property).congr'
    filter_upwards [he] with j hj
    exact (hFval (hj.2 hxW)).symm
  have hmem := bounded_cocompact_holomorphic_family_limit D hD hconn U hbounded
    hhol K hK hrep F atTop x₀ hFbase hFhol (fun x => G x.val) hFconv
  intro x hx
  exact hmem ⟨x,hx⟩

theorem cocompact_scaling_biholomorph_of_limits {n m : ℕ} {Γ : Type*}
    {U : Set (Affine n)} [LocallyCompactSpace U]
    (hconn : IsPreconnected U) (hbounded : Bornology.IsBounded U)
    [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ] [MulAction Γ U] [ProperSMul Γ U]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))
    (K : Set U) (hK : IsCompact K) (hrep : ∀ x : U, ∃ k ∈ K, ∃ γ : Γ, γ • k = x)
    {O : Set (Affine m)} {y₀ : Affine m} (hO : IsOpen O) (hy₀ : y₀ ∈ O)
    (A : ℕ → Set (Affine n)) (B : ℕ → Set (Affine m))
    (hAU : ∀ j, A j ⊆ U)
    (hAo : ∀ j, IsOpen ((Subtype.val : U → Affine n) ⁻¹' A j))
    (hBo : ∀ j, IsOpen (B j)) (b : ∀ j, Biholomorph (A j) (B j))
    (f : ℕ → Affine n → Affine m) (g : ℕ → Affine m → Affine n)
    (hbf : ∀ j (x : A j), f j x.val = ((b j).toHomeomorph x).val)
    (hbg : ∀ j (y : B j), g j y.val = ((b j).toHomeomorph.symm y).val)
    (F : Affine n → Affine m) (G : Affine m → Affine n)
    (hf : TendstoLocallyUniformlyOn f F atTop U)
    (hg : TendstoLocallyUniformlyOn g G atTop (connectedComponentIn O y₀))
    (hcoverA : ∀ C : Set (Affine n), IsCompact C → C ⊆ U → ∀ᶠ j in atTop, C ⊆ A j)
    (hcoverB : ∀ C : Set (Affine m), IsCompact C → C ⊆ connectedComponentIn O y₀ →
      ∀ᶠ j in atTop, C ⊆ B j)
    (hbase : ∃ C : Set U, IsCompact C ∧ ∀ᶠ j in atTop, g j y₀ ∈ Subtype.val '' C)
    (hexcluded : ∀ y ∉ O, ∃ a : ℕ → Affine m,
      Tendsto a atTop (𝓝 y) ∧ ∀ᶠ j in atTop, a j ∉ B j) :
    Nonempty (Biholomorph U (connectedComponentIn O y₀)) := by
  have hD := hO.connectedComponentIn (x := y₀)
  have hgj : ∀ j, AnalyticOnNhd ℂ (g j) (B j) := by
    intro j
    apply HolomorphicOnSubset.analyticOnNhd_of_open (hBo j)
    convert (b j).holomorphic_invFun using 1
    funext y
    exact hbg j y
  have hgm : ∀ j, MapsTo (g j) (B j) U := by
    intro j y hy
    rw [hbg j ⟨y,hy⟩]
    exact hAU j ((b j).toHomeomorph.symm ⟨y,hy⟩).property
  have hGmap : MapsTo G (connectedComponentIn O y₀) U := by
    refine bounded_cocompact_expanding_limit_mem _ hD
      isPreconnected_connectedComponentIn U hbounded hhol K hK hrep g G
      ⟨y₀,mem_connectedComponentIn hy₀⟩ hbase ?_ ?_
    · intro y hy
      obtain ⟨r,hr,hrD⟩ := Metric.mem_nhds_iff.mp (hD.mem_nhds hy)
      have hclosed : closedBall y (r/2) ⊆ connectedComponentIn O y₀ :=
        (closedBall_subset_ball (by linarith)).trans hrD
      refine ⟨ball y (r/2),isOpen_ball,mem_ball_self (half_pos hr),
        ball_subset_closedBall.trans hclosed,?_⟩
      filter_upwards [hcoverB _ (isCompact_closedBall _ _) hclosed] with j hj
      exact ⟨(hgj j).mono (ball_subset_closedBall.trans hj),
        (hgm j).mono_left (ball_subset_closedBall.trans hj)⟩
    · intro y hy
      exact hg.tendsto_at hy
  exact scaling_biholomorph_expanding hy₀ hconn hO A B hAU hAo hBo b
    hbf hbg hf hg hcoverA hcoverB hGmap hexcluded

theorem smooth_of_expanding_biholomorphisms {n m : ℕ} {U : Set (Affine n)}
    (A : ℕ → Set (Affine n)) (B : ℕ → Set (Affine m))
    (hAU : ∀ j, A j ⊆ U)
    (hAo : ∀ j, IsOpen ((Subtype.val : U → Affine n) ⁻¹' A j))
    (hBo : ∀ j, IsOpen (B j)) (b : ∀ j, Biholomorph (A j) (B j))
    (hcover : ∀ x ∈ U, ∀ᶠ j in atTop, x ∈ A j) : IsSmooth U := by
  intro x
  obtain ⟨j,hj⟩ := (hcover x.val x.property).exists
  exact ⟨m,A j,hAU j,hAo j,hj,B j,hBo j,⟨b j⟩⟩

theorem forward_local_data_of_compact_bounds {n m : ℕ} {U : Set (Affine n)}
    [LocallyCompactSpace U]
    (A : ℕ → Set (Affine n)) (B : ℕ → Set (Affine m))
    (b : ∀ j, Biholomorph (A j) (B j))
    (f : ℕ → Affine n → Affine m)
    (hbf : ∀ j (x : A j), f j x.val = ((b j).toHomeomorph x).val)
    (hcover : ∀ C : Set (Affine n), IsCompact C → C ⊆ U → ∀ᶠ j in atTop, C ⊆ A j)
    (hbound : ∀ C : Set (Affine n), IsCompact C → C ⊆ U →
      ∃ M : ℝ, 0 < M ∧ ∀ᶠ j in atTop, ∀ x ∈ C, ‖f j x‖ ≤ M) :
    ∀ p : U, ∃ V : Set (Affine n), V ⊆ U ∧
      IsOpen ((Subtype.val : U → Affine n) ⁻¹' V) ∧ p.val ∈ V ∧
      ∃ M : ℝ, 0 < M ∧ ∀ᶠ j in atTop,
        HolomorphicOnSubset V (fun x => f j x) ∧ ∀ y ∈ V, ‖f j y‖ ≤ M := by
  intro p
  obtain ⟨C,hC,hCp⟩ := exists_compact_mem_nhds p
  let V := Subtype.val '' interior C
  have hVU : V ⊆ U := by rintro x ⟨q,_,rfl⟩; exact q.property
  have hVo : IsOpen ((Subtype.val : U → Affine n) ⁻¹' V) := by
    rw [show ((Subtype.val : U → Affine n) ⁻¹' V) = interior C from
      preimage_image_eq _ Subtype.val_injective]
    exact isOpen_interior
  have hpV : p.val ∈ V := ⟨p,mem_interior_iff_mem_nhds.mpr hCp,rfl⟩
  have hCU : Subtype.val '' C ⊆ U := by rintro x ⟨q,_,rfl⟩; exact q.property
  have hVC : V ⊆ Subtype.val '' C := image_mono interior_subset
  have hC' := hC.image continuous_subtype_val
  obtain ⟨M,hM,hMbound⟩ := hbound _ hC' hCU
  refine ⟨V,hVU,hVo,hpV,M,hM,?_⟩
  filter_upwards [hcover _ hC' hCU,hMbound] with j hj hMj
  have hfhol : HolomorphicOnSubset (A j) (fun x => f j x) := by
    convert (b j).holomorphic_toFun using 1
    funext x
    exact hbf j x
  exact ⟨hfhol.restrict (hVC.trans hj),fun y hy => hMj y (hVC hy)⟩

end Release061

end

end OAI
