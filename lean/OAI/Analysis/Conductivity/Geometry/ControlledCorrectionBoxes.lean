import Mathlib
import OAI.Analysis.Conductivity.Sobolev.LocalPhysicalCorrectionBound

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise

structure ControlledCorrectionBox (u : Coord3 → Fin 2 → ℝ) (U : Set Coord3)
    extends RegularCorrectionBox u U where
  outerLower : Coord3
  outerUpper : Coord3
  lower_gap : ∀ i,outerLower i<lower i
  upper_gap : ∀ i,upper i<outerUpper i
  closed_subset : closedCorrectionBox outerLower outerUpper⊆chart.source

namespace ControlledCorrectionBox
variable {u : Coord3 → Fin 2 → ℝ} {U : Set Coord3}
abbrev region (B : ControlledCorrectionBox u U) : Set Coord3 := B.toRegularCorrectionBox.region
lemma region_open (B : ControlledCorrectionBox u U) : IsOpen B.region :=
  B.toRegularCorrectionBox.region_open
lemma region_nonempty (B : ControlledCorrectionBox u U) : B.region.Nonempty :=
  B.toRegularCorrectionBox.region_nonempty
lemma region_subset (B : ControlledCorrectionBox u U) : B.region⊆U :=
  B.toRegularCorrectionBox.region_subset
lemma region_bounded (B : ControlledCorrectionBox u U) : Bornology.IsBounded B.region :=
  ((closedCorrectionBox_compact B.outerLower B.outerUpper).image_of_continuousOn
    (B.chart.continuousOn.mono B.closed_subset)).isBounded.subset
      (image_mono (correctionBox_subset_closed (fun i => (B.lower_gap i).le) (fun i => (B.upper_gap i).le)))
end ControlledCorrectionBox

lemma exists_controlled_correction_box
    {u : Coord3 → Fin 2 → ℝ} (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u)
    {U : Set Coord3} (hU : IsOpen U) {p : Coord3} (hp : p∈U)
    (hD : Function.Surjective (fderiv ℝ u p)) :
    ∃ B : ControlledCorrectionBox u U,p∈B.region := by
  obtain ⟨X,hpX,hXU,hX,hXi,he⟩ := exists_regular_potential_coordinates hu p hD hU hp
  let x := X.symm p
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp X.open_source x (X.map_target hpX)
  let a : Coord3 := fun i => x i-ε/3
  let b : Coord3 := fun i => x i+ε/3
  let c : Coord3 := fun i => x i-2*ε/3
  let d : Coord3 := fun i => x i+2*ε/3
  have hc : closedCorrectionBox c d⊆X.source := by
    intro y hy
    apply hball
    rw [Metric.mem_ball,dist_pi_lt_iff hε]
    intro i
    rw [Real.dist_eq,abs_lt]
    have hi : c i≤y i ∧ y i≤d i := by
      fin_cases i
      · exact hy.1.1
      · exact hy.1.2
      · exact hy.2
    dsimp [c,d] at hi
    constructor <;> linarith
  have hca : ∀ i,c i<a i := fun i => by dsimp [c,a]; linarith
  have hbd : ∀ i,b i<d i := fun i => by dsimp [b,d]; linarith
  let B : ControlledCorrectionBox u U :=
    ⟨⟨X,a,b,fun i => by dsimp [a,b]; linarith,
      (correctionBox_subset_closed (fun i => (hca i).le) (fun i => (hbd i).le)).trans hc,
      hX,hXi.contDiffOn,fun _ _ => congrFun he _,hXU⟩,c,d,hca,hbd,hc⟩
  refine ⟨B,x,?_,X.right_inv hpX⟩
  exact mem_correctionBox.mpr (fun i => by change x i-ε/3<x i ∧ x i<x i+ε/3; constructor <;> linarith)

def BoundedPhysicallyCorrectable (u : Coord3 → Fin 2 → ℝ) (U : Set Coord3)
    (r : PhysicalSourcePair) (N : ℝ) : Prop :=
  ∃ H : Coord3 → Mat3,ContDiff ℝ (↑(⊤:ℕ∞)) H ∧ HasCompactSupport H ∧
    tsupport H⊆U ∧ (∀ x,(H x).IsSymm) ∧ (∀ j,symmetricSource H u j=r j) ∧
    ∀ x,‖H x‖≤N

namespace BoundedPhysicallyCorrectable
variable {u : Coord3 → Fin 2 → ℝ} {U : Set Coord3} {r s : PhysicalSourcePair} {M N : ℝ}
lemma mono (h : BoundedPhysicallyCorrectable u U r M) (hMN : M≤N) :
    BoundedPhysicallyCorrectable u U r N := by
  obtain ⟨H,hH,hc,hs,hsy,hr,hb⟩ := h
  exact ⟨H,hH,hc,hs,hsy,hr,fun x => (hb x).trans hMN⟩
lemma zero (hN : 0≤N) : BoundedPhysicallyCorrectable u U 0 N := by
  refine ⟨0,contDiff_const,HasCompactSupport.zero,by simp [tsupport_zero],fun _ => Matrix.isSymm_zero,?_,?_⟩
  · intro j; funext x; simp [symmetricSource,coordinateDivergence,Matrix.col]
  · intro x; simpa using hN
lemma add (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u)
    (hr : BoundedPhysicallyCorrectable u U r M) (hs : BoundedPhysicallyCorrectable u U s N) :
    BoundedPhysicallyCorrectable u U (r+s) (M+N) := by
  obtain ⟨H,hH,hHc,hHs,hHsy,hHr,hHb⟩ := hr
  obtain ⟨K,hK,hKc,hKs,hKsy,hKr,hKb⟩ := hs
  refine ⟨H+K,hH.add hK,hHc.add hKc,(tsupport_add H K).trans (union_subset hHs hKs),
    fun x => (hHsy x).add (hKsy x),?_,fun x => (norm_add_le _ _).trans (add_le_add (hHb x) (hKb x))⟩
  intro j
  rw [symmetricSource_add hH hK hu j,hHr j,hKr j]
  rfl
lemma correctable (h : BoundedPhysicallyCorrectable u U r N) : PhysicallyCorrectable u U r := by
  obtain ⟨H,hH,hc,hs,hsy,hr,_⟩ := h
  exact ⟨H,hH,hc,hs,hsy,hr⟩
end BoundedPhysicallyCorrectable

lemma ControlledCorrectionBox.bounded_solver
    {u : Coord3 → Fin 2 → ℝ} (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u) {U : Set Coord3}
    (B : ControlledCorrectionBox u U) :
    ∃ L : ℝ,0<L ∧ ∀ r : PhysicalSourcePair,CompactSmoothPair r → PairSupported r B.region →
      physicalSourceMoment u r=0 → ∀ M : ℝ,0≤M → (∀ j,UniformC1Bound (r j) M) →
      BoundedPhysicallyCorrectable u U r (L*M) := by
  obtain ⟨L,hL,solve⟩ := local_physical_symmetric_correction_C0 B.chart B.smooth B.inverse_smooth
    B.widths B.lower_gap B.upper_gap B.closed_subset u hu B.potentials
  refine ⟨L,hL,fun r hr hs hm M hM hb => ?_⟩
  have hz (j : Fin 2) : (∫ x,r j x)=0 := by
    fin_cases j
    · exact congrFun hm 0
    · exact congrFun hm 1
  obtain ⟨H,hH,hc,hsub,hsy,hsrc,hbound⟩ := solve r (fun j => (hr j).1) (fun j => (hr j).2)
    hs hz (congrFun hm 2) M hM hb
  exact ⟨H,hH,hc,hsub.trans B.target_subset,hsy,hsrc,hbound⟩

end ScalarConductivity

end
end

end OAI
