import Mathlib
import OAI.Geometry.BallPacking.Annuli.AnnularChartNormalization
import OAI.Geometry.BallPacking.SurfaceArea.AnnularSecondPositivity

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold
open MeasureTheory
section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

namespace SurfaceCoordinateBox

def Inside (U : Set M) := {B : SurfaceCoordinateBox M // B.compactCarrier ⊆ U}

theorem interior_overlap_chain {U : Set M} (hU : IsOpen U) (hc : IsPreconnected U)
    (B C : Inside U) :
    Relation.ReflTransGen (fun A D : Inside U => (A.1.carrier ∩ D.1.carrier).Nonempty) B C := by
  let := Subtype.preconnectedSpace hc
  let V : Inside U → Set U := fun D => Subtype.val ⁻¹' D.1.carrier
  have ho (D : Inside U) : IsOpen (V D) := D.1.isOpen_carrier.preimage continuous_subtype_val
  have hcover (x : U) : ∃ D, x ∈ V D := by
    obtain ⟨D,hx,hDU⟩ := exists_compactCarrier_subset hU x.property
    exact ⟨⟨D,hDU⟩,hx⟩
  have hn (D : Inside U) : (V D).Nonempty := by
    obtain ⟨x,hx⟩ := D.1.nonempty_carrier
    exact ⟨⟨x,D.2 (D.1.carrier_subset_compactCarrier hx)⟩,hx⟩
  have hh := connected_cover_overlap_chain ho hcover (hn B) (hn C)
  induction hh with
  | refl => exact Relation.ReflTransGen.refl
  | @tail A D _ hAD ih =>
    obtain ⟨x,hxA,hxD⟩ := hAD
    exact ih.tail ⟨x.1,hxA,hxD⟩

theorem finite_partition_inside [IsManifold 𝓘(ℝ,Plane) ∞ M] [T2Space M]
    [SigmaCompactSpace M] {K U : Set M} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) :
    ∃ (s : Finset (Inside U))
      (ρ : SmoothPartitionOfUnity s 𝓘(ℝ,Plane) M K),
      ρ.IsSubordinate (fun B => B.1.1.carrier) := by
  classical
  have hcover : K ⊆ ⋃ B : Inside U, B.1.carrier := by
    intro x hx
    obtain ⟨B,hxB,hBU⟩ := exists_compactCarrier_subset hU (hKU hx)
    exact mem_iUnion.mpr ⟨⟨B,hBU⟩,hxB⟩
  obtain ⟨s,hs⟩ := hK.elim_finite_subcover (fun B : Inside U => B.1.carrier)
    (fun B => B.1.isOpen_carrier) hcover
  obtain ⟨ρ,hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ,Plane) hK.isClosed
    (fun B : s => B.1.1.carrier) (fun B => B.1.1.isOpen_carrier) (by
      intro x hx
      obtain ⟨B,hBs,hxB⟩ := mem_iUnion₂.mp (hs hx)
      exact mem_iUnion.mpr ⟨⟨B,hBs⟩,hxB⟩)
  exact ⟨s,ρ,hρ⟩

end SurfaceCoordinateBox

end
section

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M] [T2Space M]

def HasInteriorPrimitiveFamily (U : Set M) (Ω : P → ManifoldTwoForm Plane M) : Prop :=
  ∃ L : Set M, IsCompact L ∧ L ⊆ U ∧ ∃ α : P → ManifoldOneForm Plane M,
    IsPrimitiveFamily Ω α ∧ ∀ p x,x∉L→α p x=0

omit [FiniteDimensional ℝ P] [IsManifold 𝓘(ℝ,Plane) ∞ M] [T2Space M] in
theorem HasInteriorPrimitiveFamily.add {U : Set M} {Ω Λ : P → ManifoldTwoForm Plane M}
    (hΩ : HasInteriorPrimitiveFamily U Ω) (hΛ : HasInteriorPrimitiveFamily U Λ) :
    HasInteriorPrimitiveFamily U (Ω+Λ) := by
  obtain ⟨K,hK,hKU,α,hα,hzα⟩ := hΩ
  obtain ⟨L,hL,hLU,β,hβ,hzβ⟩ := hΛ
  refine ⟨K∪L,hK.union hL,union_subset hKU hLU,α+β,hα.add hβ,?_⟩
  intro p x hx
  change α p x+β p x=0
  rw [hzα p x (fun hk => hx (Or.inl hk)),hzβ p x (fun hl => hx (Or.inr hl)),add_zero]

theorem surface_box_difference_inside {U : Set M} (B : SurfaceCoordinateBox M)
    (hBU : B.compactCarrier ⊆ U)
    {Ω Λ : ManifoldTwoForm Plane M} (hΩ : SmoothTwoForm Ω) (hΛ : SmoothTwoForm Λ)
    (hsΩ : ∀ x u v,Ω x u v= -Ω x v u) (hsΛ : ∀ x u v,Λ x u v= -Λ x v u)
    {K L : Set M} (hK : IsCompact K) (hL : IsCompact L)
    (hKB : K⊆B.carrier) (hLB : L⊆B.carrier)
    (hzΩ : ∀ x,x∉K→Ω x=0) (hzΛ : ∀ x,x∉L→Λ x=0)
    (hm : chartMass B.center Ω=chartMass B.center Λ) :
    HasInteriorPrimitiveFamily U (fun _ : P => Ω-Λ) := by
  have hs : ∀ p : P,∀ x u v,(Ω-Λ) x u v= -(Ω-Λ) x v u := by
    intro _ x u v
    change Ω x u v-Λ x u v= -(Ω x v u-Λ x v u)
    rw [hsΩ x u v,hsΛ x u v]; ring
  have hz : ∀ p : P,∀ x,x∉K∪L→(Ω-Λ) x=0 := by
    intro _ x hx
    change Ω x-Λ x=0
    rw [hzΩ x (fun hk => hx (Or.inl hk)),hzΛ x (fun hl => hx (Or.inr hl))]
    apply ContinuousLinearMap.ext
    intro u
    apply ContinuousLinearMap.ext
    intro v
    exact sub_self (0 : ℝ)
  have hm0 : ∀ _ : P,chartMass B.center (Ω-Λ)=0 := by
    intro _
    rw [chartMass_sub (hΩ.coefficient_integrable B.center hK (fun x hx => (hKB hx).1) hzΩ)
      (hΛ.coefficient_integrable B.center hL (fun x hx => (hLB hx).1) hzΛ),hm,sub_self]
  have hh := boxCovectorOperator_spec B
    ((SmoothTwoFormFamily.const (P := P) hΩ).sub (SmoothTwoFormFamily.const hΛ))
    hs (hK.union hL) (union_subset hKB hLB) hz hm0
  exact ⟨B.compactCarrier,B.isCompact_compactCarrier,hBU,
    (fun _ : P => boxCovectorOperator B (Ω-Λ)),⟨hh.1,hh.2.2⟩,hh.2.1⟩

theorem surface_overlap_difference_inside {U : Set M} (hpos : PositivePlaneTransitions M)
    {B C : SurfaceCoordinateBox M} (hBU : B.compactCarrier⊆U) (hCU : C.compactCarrier⊆U)
    (β : BoxUnitBump B) (γ : BoxUnitBump C) (hBC : (B.carrier∩C.carrier).Nonempty) :
    HasInteriorPrimitiveFamily U (fun _ : P => β.form-γ.form) := by
  obtain ⟨x,hx⟩ := hBC
  obtain ⟨D,_,hD⟩ := SurfaceCoordinateBox.exists_compactCarrier_subset
    (B.isOpen_carrier.inter C.isOpen_carrier) hx
  obtain ⟨δ⟩ := D.exists_unit_bump
  have hδB : δ.supportSet⊆B.carrier :=
    δ.support_subset.trans (D.carrier_subset_compactCarrier.trans (hD.trans inter_subset_left))
  have hδC : δ.supportSet⊆C.carrier :=
    δ.support_subset.trans (D.carrier_subset_compactCarrier.trans (hD.trans inter_subset_right))
  have h1 : HasInteriorPrimitiveFamily U (fun _ : P => β.form-δ.form) :=
    surface_box_difference_inside B hBU β.smooth δ.smooth β.skew δ.skew β.compact_supportSet
      δ.compact_supportSet β.support_subset hδB β.zero_off δ.zero_off
      (β.unit_mass.trans (δ.mass_in_chart hpos B.center (fun z hz => (hδB hz).1)).symm)
  have h2 : HasInteriorPrimitiveFamily U (fun _ : P => δ.form-γ.form) :=
    surface_box_difference_inside C hCU δ.smooth γ.smooth δ.skew γ.skew δ.compact_supportSet
      γ.compact_supportSet hδC γ.support_subset δ.zero_off γ.zero_off
      ((δ.mass_in_chart hpos C.center (fun z hz => (hδC hz).1)).trans γ.unit_mass.symm)
  have he : (fun _ : P => β.form-δ.form)+(fun _ : P => δ.form-γ.form)=
      (fun _ : P => β.form-γ.form) := by
    funext p; simp only [Pi.add_apply]; abel
  exact he ▸ h1.add h2

theorem surface_bump_difference_inside {U : Set M} (hU : IsOpen U) (hc : IsPreconnected U)
    (hpos : PositivePlaneTransitions M) {B C : SurfaceCoordinateBox.Inside U}
    (β : BoxUnitBump B.1) (γ : BoxUnitBump C.1) :
    HasInteriorPrimitiveFamily U (fun _ : P => β.form-γ.form) := by
  have hchain := SurfaceCoordinateBox.interior_overlap_chain hU hc B C
  revert γ
  induction hchain with
  | refl =>
    intro γ
    exact surface_box_difference_inside B.1 B.2 β.smooth γ.smooth β.skew γ.skew
      β.compact_supportSet γ.compact_supportSet β.support_subset γ.support_subset
      β.zero_off γ.zero_off (β.unit_mass.trans γ.unit_mass.symm)
  | @tail C D _ hCD ih =>
    intro γ
    obtain ⟨δ⟩ := C.1.exists_unit_bump
    have h1 := ih δ
    have h2 : HasInteriorPrimitiveFamily U (fun _ : P => δ.form-γ.form) :=
      surface_overlap_difference_inside hpos C.2 D.2 δ γ hCD
    have he : (fun _ : P => β.form-δ.form)+(fun _ : P => δ.form-γ.form)=
        (fun _ : P => β.form-γ.form) := by
      funext p; simp only [Pi.add_apply]; abel
    exact he ▸ h1.add h2

theorem exists_interior_mass_transfer_data {I : Type*} {U : Set M}
    (hU : IsOpen U) (hc : IsPreconnected U) (hpos : PositivePlaneTransitions M)
    (B : I → SurfaceCoordinateBox.Inside U) (B₀ : SurfaceCoordinateBox.Inside U) :
    ∃ D : SurfaceMassTransferData (fun i => (B i).1) B₀.1,
      ∀ i,D.supportSet i⊆U := by
  classical
  let β (i : I) : BoxUnitBump (B i).1 := Classical.choice (B i).1.exists_unit_bump
  obtain ⟨β₀⟩ := B₀.1.exists_unit_bump
  have hh (i : I) := surface_bump_difference_inside (P := ℝ) hU hc hpos (β i) β₀
  choose L hL hLU α hα hz using hh
  refine ⟨⟨β,β₀,(fun i => α i 0),L,hL,(fun i => hz i 0),?_⟩,hLU⟩
  intro i
  exact (hα i).const_slice (P := ℝ) 0

end
section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  {I : Type*} {K L : Set M}

def restrictSurfacePartition (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    (hLK : L⊆K) : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M L where
  toFun := ρ.toFun
  locallyFinite' := ρ.locallyFinite'
  nonneg' := ρ.nonneg'
  sum_eq_one' := fun _ hx => ρ.sum_eq_one (hLK hx)
  sum_le_one' := ρ.sum_le_one'

theorem restrictSurfacePartition_subordinate
    (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K) (hLK : L⊆K)
    {V : I → Set M} (hρ : ρ.IsSubordinate V) :
    (restrictSurfacePartition ρ hLK).IsSubordinate V := hρ

theorem partitionFormMass_restrict [Fintype I]
    (B : I → SurfaceCoordinateBox M) (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    (hLK : L⊆K) (Ω : ManifoldTwoForm Plane M) :
    partitionFormMass B (restrictSurfacePartition ρ hLK) Ω=partitionFormMass B ρ Ω := rfl

end

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M] [T2Space M] [SigmaCompactSpace M]
  {I : Type*} [Fintype I] {K L U : Set M}

theorem interior_surface_primitive (hU : IsOpen U) (hc : IsPreconnected U)
    (hne : U.Nonempty) (hpos : PositivePlaneTransitions M)
    (hL : IsCompact L) (hLU : L⊆U) (hLK : L⊆K)
    (B : I → SurfaceCoordinateBox M) (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    (hρ : ρ.IsSubordinate (fun i => (B i).carrier))
    {Ω : P → ManifoldTwoForm Plane M} (hΩ : SmoothTwoFormFamily Ω)
    (hskew : ∀ p x u v,Ω p x u v= -Ω p x v u)
    (hz : ∀ p x,x∉L→Ω p x=0)
    (hmass : ∀ p,partitionFormMass B ρ (Ω p)=0) :
    HasInteriorPrimitiveFamily U Ω := by
  obtain ⟨s,ν,hν⟩ := SurfaceCoordinateBox.finite_partition_inside hL hU hLU
  let C : s → SurfaceCoordinateBox.Inside U := fun i => i.1
  obtain ⟨x,hx⟩ := hne
  obtain ⟨B₀,_,hB₀⟩ := SurfaceCoordinateBox.exists_compactCarrier_subset hU hx
  obtain ⟨D,hD⟩ := exists_interior_mass_transfer_data hU hc hpos C ⟨B₀,hB₀⟩
  have hm (p : P) : partitionFormMass (fun i => (C i).1) ν (Ω p)=0 := by
    rw [← partitionFormMass_independent hpos hL B (fun i => (C i).1)
      (restrictSurfacePartition ρ hLK) ν
      (restrictSurfacePartition_subordinate ρ hLK hρ) hν (hΩ.eval p) (hskew p) (hz p)]
    exact hmass p
  have hh := surfaceCovectorOperator_spec hL (fun i => (C i).1) B₀ ν hν D hΩ hskew hz hm
  refine ⟨surfaceCovectorSupport (fun i => (C i).1) B₀ D,
    surfaceCovectorSupport_compact _ _ _,?_,
    (fun p => surfaceCovectorOperator (fun i => (C i).1) B₀ ν D (Ω p)),hh⟩
  intro z hz
  obtain ⟨i,hzi⟩ := mem_iUnion.mp hz
  exact hzi.elim (fun ht => (C i).2 ht) (fun ht => hD i ht)

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.Hamiltonian.AnnularHandleData
open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  {M : Type} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M] [T2Space M] [NormalSpace M] [SigmaCompactSpace M]
  {K : Set M}

theorem exists_normalized_surface_primitive
    (D : AnnularHandleData Plane M) {b : ℝ} (hb : b<D.width)
    (heK : D.chart.target⊆interior K) (hβK : tsupport D.dual⊆interior K)
    {Λ : ManifoldTwoForm Plane M} (hΛ : SmoothTwoForm Λ)
    (hsΛ : ∀ x v w,Λ x v w= -Λ x w v)
    {q : ℝ} {H : P → ℝ} (hH : ContDiff ℝ ∞ H)
    {κ Ξ : P → ManifoldTwoForm Plane M} {Γ₀ : P → ManifoldOneForm Plane M}
    (hΓ₀ : SmoothOneFormFamily Γ₀)
    (hdΓ₀ : ∀ p x,manifoldExteriorOneForm (Γ₀ p) x=κ p x)
    (hΞ : HasInteriorPrimitiveFamily (interior K) Ξ)
    (hformula : ∀ p,∀ x∈D.chart.target,
      κ p x+Ξ p x=q • Λ x+H p • D.density b x) :
    ∃ (Γ₁ : P → ManifoldOneForm Plane M) (γ : ManifoldOneForm Plane M) (L W : Set M),
      SmoothOneFormFamily Γ₁ ∧ IsCompact L ∧ L⊆interior K ∧ IsOpen W ∧
      D.chart '' band b⊆W ∧ W⊆D.chart.target ∧
      (∀ p x,x∉L→Γ₁ p x=Γ₀ p x) ∧
      (∀ p x,manifoldExteriorOneForm (Γ₁ p) x=κ p x+Ξ p x) ∧
      (∀ x∈D.chart.target,ContDiffAt ℝ ∞
        (chartOneForm γ x) (extChartAt 𝓘(ℝ,Plane) x x)) ∧
      (∀ x∈D.chart.target,manifoldExteriorOneForm γ x=q • Λ x) ∧
      (∀ p,∀ x∈W,Γ₁ p x=γ x+
        (intervalClock (-b) b (D.chart.symm x).1*H p) • D.dual x) := by
  obtain ⟨L₀,hL₀,hL₀K,α,hα,hαz⟩ := hΞ
  let Γ : P → ManifoldOneForm Plane M := Γ₀+α
  have hΓ : SmoothOneFormFamily Γ := by
    intro c
    simpa only [Γ,Pi.add_apply,chartOneForm_add] using (hΓ₀ c).add (hα.smooth c)
  have hdΓ (p : P) (x : M) : manifoldExteriorOneForm (Γ p) x=κ p x+Ξ p x := by
    have hx := (extChartAt 𝓘(ℝ,Plane) x).map_source (mem_extChartAt_source (I := 𝓘(ℝ,Plane)) x)
    change manifoldExteriorOneForm (Γ₀ p+α p) x=_
    rw [manifoldExteriorOneForm_add_at (hΓ₀.spatial_smooth p x hx)
      (hα.smooth.spatial_smooth p x hx),hdΓ₀ p x,hα.intrinsic p x]
  obtain ⟨γ,N,hγ,hdγ,hN,hdN,hNeq⟩ :=
    D.exists_normal_form b q hΛ hsΛ hH
  obtain ⟨Γ₁,L₁,W,hL₁,hL₁A,hW,hband,hWA,hΓ₁,hsub,_,hdΓ₁,hΓ₁N⟩ :=
    D.normalize_primitive (P := P) isOpen_univ hb
      hΓ (fun p _ x hx => hN p x hx) (fun p _ x hx =>
        (hdΓ p x).trans ((hformula p x hx).trans (hdN p x hx).symm))
  let L := L₀∪tsupport (D.dual)∪L₁
  refine ⟨Γ₁,γ,L,W,hΓ₁,(hL₀.union D.dual_compact).union hL₁,
    union_subset (union_subset hL₀K hβK) (hL₁A.trans heK),hW,hband,hWA,?_,?_,hγ,hdγ,?_⟩
  · intro p x hx
    have h0 : α p x=0 := hαz p x (fun hk => hx (Or.inl (Or.inl hk)))
    have h1 : (Γ₁ p-Γ p) x=0 := by
      apply notMem_support.mp
      intro hs
      have hmem := hsub p hs
      exact hmem.elim (fun h => hx (Or.inl (Or.inr h))) (fun h => hx (Or.inr h))
    have heq : Γ₁ p x=Γ p x := sub_eq_zero.mp h1
    simpa only [Γ,Pi.add_apply,h0,add_zero] using heq
  · intro p x
    exact (hdΓ₁ p (mem_univ p) x).trans (hdΓ p x)
  · intro p x hx
    exact (hΓ₁N p (mem_univ p) x hx).trans (hNeq p x (hWA hx))

end PackingSufficiencySupport.Hamiltonian.AnnularHandleData

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold
open MeasureTheory
section

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

theorem SmoothTwoFormFamily.coefficient_smul {Ω : P → ManifoldTwoForm E M}
    (hΩ : SmoothTwoFormFamily Ω) {f : P × M → ℝ}
    (hf : ContMDiff (𝓘(ℝ,P).prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ) ∞ f) :
    SmoothTwoFormFamily (fun p x => f (p,x) • Ω p x) := by
  let : IsBoundedSMul ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
    NormedSpace.toIsBoundedSMul (𝕜 := ℝ) (E := E →L[ℝ] E →L[ℝ] ℝ)
  intro c q hq
  have hi : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) ∞
      (extChartAt 𝓘(ℝ,E) c).symm q.2 :=
    (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,E)) (n := ∞) c).contMDiffAt
      ((isOpen_extChartAt_target c).mem_nhds hq.2)
  have hinv : ContMDiffAt (𝓘(ℝ,P).prod 𝓘(ℝ,E)) (𝓘(ℝ,P).prod 𝓘(ℝ,E)) ∞
      (fun z : P × E => (z.1,(extChartAt 𝓘(ℝ,E) c).symm z.2)) q :=
    contMDiffAt_fst.prodMk (hi.comp q contMDiffAt_snd)
  have hfs : ContDiffAt ℝ ∞
      (fun z : P × E => f (z.1,(extChartAt 𝓘(ℝ,E) c).symm z.2)) q :=
    by
      have hmd := hf.contMDiffAt.comp q hinv
      rw [← modelWithCornersSelf_prod,chartedSpaceSelf_prod] at hmd
      exact hmd.contDiffAt
  have hΩs := (hΩ c).contDiffAt
    ((isOpen_univ.prod (isOpen_extChartAt_target c)).mem_nhds hq)
  simpa only [chartTwoForm_spatial_smul,Pi.smul_def'] using (hfs.smul hΩs).contDiffWithinAt

end
section

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M] [T2Space M] [NormalSpace M] [SigmaCompactSpace M]

theorem exists_interior_boundary_cutoff {K V : Set M} (hK : IsCompact K)
    (hV : IsOpen V) (hfront : frontier K⊆V) :
    ∃ ψ : M → ℝ, ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ ψ ∧
      IsCompact (tsupport ψ) ∧ tsupport ψ⊆interior K ∧
      (∀ x∈K, x∉V→ψ x=1) := by
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace E M
  have hL : IsCompact (K\V) := hK.diff hV
  have hLK : K\V⊆interior K := by
    intro x hx
    by_contra hn
    exact hx.2 (hfront ⟨subset_closure hx.1,hn⟩)
  obtain ⟨D,hD,hLD,hDK⟩ := exists_compact_between hL isOpen_interior hLK
  obtain ⟨ψ,hψ1,hψ0,_⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (n := (⊤ : ℕ∞)) 𝓘(ℝ,E) hL.isClosed hLD
  have hs : tsupport (ψ : M → ℝ)⊆D :=
    closure_minimal (fun x hx => by by_contra hn; exact hx (hψ0 x hn)) hD.isClosed
  refine ⟨ψ,ψ.contMDiff,hD.of_isClosed_subset (isClosed_tsupport _) hs,hs.trans hDK,?_⟩
  intro x hx hn
  exact (subset_of_mem_nhdsSet hψ1 ⟨hx,hn⟩)

end
section

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M] [T2Space M] [NormalSpace M] [SigmaCompactSpace M]

theorem exists_interior_coefficient_difference {K V : Set M}
    (hK : IsCompact K) (hV : IsOpen V) (hfront : frontier K⊆V)
    {a b : P × M → ℝ}
    (ha : ContMDiff (𝓘(ℝ,P).prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ) ∞ a)
    (hb : ContMDiff (𝓘(ℝ,P).prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ) ∞ b)
    (hgerm : ∀ p x,x∈V→a (p,x)=b (p,x)) :
    ∃ (L : Set M) (d : P × M → ℝ),IsCompact L ∧ L⊆interior K ∧
      ContMDiff (𝓘(ℝ,P).prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ) ∞ d ∧
      (∀ p x,x∈K→d (p,x)=a (p,x)-b (p,x)) ∧
      (∀ p x,x∉L→d (p,x)=0) := by
  obtain ⟨ψ,hψ,hL,hLK,hψ1⟩ := exists_interior_boundary_cutoff (E := E) hK hV hfront
  refine ⟨tsupport ψ,(fun q => ψ q.2*(a q-b q)),hL,hLK,
    (hψ.comp contMDiff_snd).mul (ha.sub hb),?_,?_⟩
  · intro p x hx
    change ψ x * (a (p,x)-b (p,x))=a (p,x)-b (p,x)
    by_cases hv : x∈V
    · rw [hgerm p x hv,sub_self,mul_zero]
    · rw [hψ1 x hx hv,one_mul]
  · intro p x hx
    change ψ x * (a (p,x)-b (p,x))=0
    rw [image_eq_zero_of_notMem_tsupport hx,zero_mul]

end
section

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M] [MeasurableSpace M] [BorelSpace M]
  {I : Type*} [Fintype I] {K L : Set M}

theorem interior_difference_mass
    (B : I → SurfaceCoordinateBox M) (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    (hρ : ρ.IsSubordinate (fun i => (B i).carrier)) (hK : MeasurableSet K)
    {Λ : ManifoldTwoForm Plane M} (hΛ : SmoothTwoForm Λ)
    (hpos : ∀ c y,y∈(extChartAt 𝓘(ℝ,Plane) c).target→
      0≤chartTwoForm Λ c y (1,0) (0,1))
    {a b d : P × M → ℝ}
    (ha : ContMDiff (𝓘(ℝ,P).prod 𝓘(ℝ,Plane)) 𝓘(ℝ,ℝ) ∞ a)
    (hb : ContMDiff (𝓘(ℝ,P).prod 𝓘(ℝ,Plane)) 𝓘(ℝ,ℝ) ∞ b)
    (hd : ContMDiff (𝓘(ℝ,P).prod 𝓘(ℝ,Plane)) 𝓘(ℝ,ℝ) ∞ d)
    (hLK : L⊆K) (hz : ∀ p x,x∉L→d (p,x)=0)
    (he : ∀ p x,x∈K→d (p,x)=a (p,x)-b (p,x)) (p : P) :
    partitionFormMass B ρ (fun x => d (p,x) • Λ x)=
      restrictedPartitionFormMass B ρ K (fun x => a (p,x) • Λ x)-
      restrictedPartitionFormMass B ρ K (fun x => b (p,x) • Λ x) := by
  have ha' : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,ℝ) ∞ (fun x => a (p,x)) :=
    ha.comp (contMDiff_const.prodMk contMDiff_id)
  have hb' : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,ℝ) ∞ (fun x => b (p,x)) :=
    hb.comp (contMDiff_const.prodMk contMDiff_id)
  have hd' : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,ℝ) ∞ (fun x => d (p,x)) :=
    hd.comp (contMDiff_const.prodMk contMDiff_id)
  rw [← integral_partitionAreaMeasure B ρ hρ hΛ hpos hd']
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
    (s := K) (fun x hx => hz p x (fun hl => hx (hLK hl)))]
  calc
    (∫ x in K,d (p,x) ∂partitionAreaMeasure B ρ Λ)=
        ∫ x in K,(a (p,x)-b (p,x)) ∂partitionAreaMeasure B ρ Λ :=
      setIntegral_congr_fun hK (he p)
    _ = (∫ x in K,a (p,x) ∂partitionAreaMeasure B ρ Λ)-
        ∫ x in K,b (p,x) ∂partitionAreaMeasure B ρ Λ :=
      integral_sub (smooth_integrable_partitionAreaMeasure B ρ hρ hΛ hpos ha').integrableOn
        (smooth_integrable_partitionAreaMeasure B ρ hρ hΛ hpos hb').integrableOn
    _ = _ := by
      rw [integral_partitionAreaMeasure_restrict B ρ hρ hΛ hpos hK ha',
        integral_partitionAreaMeasure_restrict B ρ hρ hΛ hpos hK hb']

theorem restricted_form_mass_nonneg
    (B : I → SurfaceCoordinateBox M) (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    (hρ : ρ.IsSubordinate (fun i => (B i).carrier)) (hK : MeasurableSet K)
    {Λ : ManifoldTwoForm Plane M} (hΛ : SmoothTwoForm Λ)
    (hpos : ∀ c y,y∈(extChartAt 𝓘(ℝ,Plane) c).target→
      0≤chartTwoForm Λ c y (1,0) (0,1))
    {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,ℝ) ∞ f)
    (hfpos : ∀ x∈K,0≤f x) :
    0≤restrictedPartitionFormMass B ρ K (fun x => f x • Λ x) := by
  rw [← integral_partitionAreaMeasure_restrict B ρ hρ hΛ hpos hK hf]
  exact setIntegral_nonneg hK hfpos

end

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M]
  {I : Type*} [Fintype I] {K : Set M}

theorem partitionFormMass_smooth (hK : IsCompact K)
    (B : I → SurfaceCoordinateBox M) (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    (hρ : ρ.IsSubordinate (fun i => (B i).carrier))
    {Ω : P → ManifoldTwoForm Plane M} (hΩ : SmoothTwoFormFamily Ω)
    (hz : ∀ p x,x∉K→Ω p x=0) :
    ContDiff ℝ ∞ (fun p => partitionFormMass B ρ (Ω p)) := by
  apply ContDiff.sum
  intro i _
  exact chartMass_smooth (partitionTwoForm_smooth ρ hΩ i (B i).center)
    (hK.inter_right (isClosed_tsupport (ρ i)))
    (fun _ hx => (hρ i hx.2).1) (partitionTwoForm_zero ρ hz i)

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P] in
theorem partitionFormMass_sub (hK : IsCompact K)
    (B : I → SurfaceCoordinateBox M) (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K)
    (hρ : ρ.IsSubordinate (fun i => (B i).carrier))
    {Ω Λ : ManifoldTwoForm Plane M} (hΩ : SmoothTwoForm Ω) (hΛ : SmoothTwoForm Λ)
    (hzΩ : ∀ x,x∉K→Ω x=0) (hzΛ : ∀ x,x∉K→Λ x=0) :
    partitionFormMass B ρ (Ω-Λ)=partitionFormMass B ρ Ω-partitionFormMass B ρ Λ := by
  have he : Ω-Λ=Ω+(-1:ℝ) • Λ := by
    funext x
    apply ContinuousLinearMap.ext
    intro u
    apply ContinuousLinearMap.ext
    intro v
    change Ω x u v-Λ x u v=Ω x u v+(-1)*Λ x u v
    ring
  rw [he,partitionFormMass_add hK B ρ hρ hΩ
    (((SmoothTwoFormFamily.const (P := ℝ) hΛ).smul contDiff_const).eval (0:ℝ))
    hzΩ (fun x hx => by
      change (-1:ℝ) • Λ x=0
      rw [hzΛ x hx]
      apply ContinuousLinearMap.ext
      intro u
      apply ContinuousLinearMap.ext
      intro v
      exact mul_zero (-1:ℝ)),
    partitionFormMass_smul]
  ring

end PackingSufficiencySupport.Hamiltonian
end

end OAI
