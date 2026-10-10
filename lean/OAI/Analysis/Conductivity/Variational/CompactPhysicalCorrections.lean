import Mathlib
import OAI.Analysis.Conductivity.Sources.SymmetricCutoffSources
import OAI.Analysis.Conductivity.Geometry.RegularPotentialCoordinates

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise

abbrev PhysicalSourcePair := Fin 2 → Coord3 → ℝ

def CompactSmoothPair (r : PhysicalSourcePair) : Prop :=
  ∀ j,ContDiff ℝ (↑(⊤:ℕ∞)) (r j) ∧ HasCompactSupport (r j)

def PairSupported (r : PhysicalSourcePair) (U : Set Coord3) : Prop :=
  ∀ j,tsupport (r j)⊆U

def physicalSourceMoment (u : Coord3 → Fin 2 → ℝ) (r : PhysicalSourcePair) : Coord3 :=
  ![∫ x,r 0 x,∫ x,r 1 x,∫ x,u x 1*r 0 x-u x 0*r 1 x]

namespace CompactSmoothPair
variable {r s : PhysicalSourcePair}
lemma zero : CompactSmoothPair 0 := fun _ => ⟨contDiff_const,HasCompactSupport.zero⟩
lemma add (hr : CompactSmoothPair r) (hs : CompactSmoothPair s) : CompactSmoothPair (r+s) :=
  fun j => ⟨(hr j).1.add (hs j).1,(hr j).2.add (hs j).2⟩
lemma sub (hr : CompactSmoothPair r) (hs : CompactSmoothPair s) : CompactSmoothPair (r-s) :=
  fun j => ⟨(hr j).1.sub (hs j).1,(hr j).2.sub (hs j).2⟩
lemma integrable (hr : CompactSmoothPair r) (j : Fin 2) : Integrable (r j) :=
  (hr j).1.continuous.integrable_of_hasCompactSupport (hr j).2
lemma torque_integrable (hr : CompactSmoothPair r) {u : Coord3 → Fin 2 → ℝ}
    (hu : Continuous u) : Integrable (fun x => u x 1*r 0 x-u x 0*r 1 x) :=
  ((continuous_apply 1 |>.comp hu).mul (hr 0).1.continuous |>.integrable_of_hasCompactSupport
    (hr 0).2.mul_left).sub
  ((continuous_apply 0 |>.comp hu).mul (hr 1).1.continuous |>.integrable_of_hasCompactSupport
    (hr 1).2.mul_left)
end CompactSmoothPair

namespace PairSupported
variable {r s : PhysicalSourcePair} {U V : Set Coord3}
lemma mono (hr : PairSupported r U) (hUV : U⊆V) : PairSupported r V :=
  fun j => (hr j).trans hUV
lemma zero : PairSupported 0 U := by intro j; simp [tsupport_zero]
lemma add (hr : PairSupported r U) (hs : PairSupported s U) : PairSupported (r+s) U :=
  fun j => (tsupport_add (r j) (s j)).trans (union_subset (hr j) (hs j))
lemma sub (hr : PairSupported r U) (hs : PairSupported s U) : PairSupported (r-s) U :=
  fun j => (tsupport_sub (r j) (s j)).trans (union_subset (hr j) (hs j))
end PairSupported

lemma physicalSourceMoment_zero (u : Coord3 → Fin 2 → ℝ) : physicalSourceMoment u 0=0 := by
  simp [physicalSourceMoment]

lemma physicalSourceMoment_add {u : Coord3 → Fin 2 → ℝ} (hu : Continuous u)
    {r s : PhysicalSourcePair} (hr : CompactSmoothPair r) (hs : CompactSmoothPair s) :
    physicalSourceMoment u (r+s)=physicalSourceMoment u r+physicalSourceMoment u s := by
  have he : (fun x => u x 1*(r+s) 0 x-u x 0*(r+s) 1 x)=
      (fun x => (u x 1*r 0 x-u x 0*r 1 x)+(u x 1*s 0 x-u x 0*s 1 x)) := by
    funext x; change u x 1*(r 0 x+s 0 x)-u x 0*(r 1 x+s 1 x)=_; ring
  ext i
  fin_cases i
  · exact integral_add (hr.integrable 0) (hs.integrable 0)
  · exact integral_add (hr.integrable 1) (hs.integrable 1)
  · change (∫ x,u x 1*(r+s) 0 x-u x 0*(r+s) 1 x)=_
    rw [he,integral_add (hr.torque_integrable hu) (hs.torque_integrable hu)]
    rfl

lemma physicalSourceMoment_sub {u : Coord3 → Fin 2 → ℝ} (hu : Continuous u)
    {r s : PhysicalSourcePair} (hr : CompactSmoothPair r) (hs : CompactSmoothPair s) :
    physicalSourceMoment u (r-s)=physicalSourceMoment u r-physicalSourceMoment u s := by
  have he := physicalSourceMoment_add hu (hr.sub hs) hs
  rw [sub_add_cancel] at he
  exact eq_sub_iff_add_eq.mpr he.symm

def PhysicallyCorrectable (u : Coord3 → Fin 2 → ℝ) (U : Set Coord3)
    (r : PhysicalSourcePair) : Prop :=
  ∃ H : Coord3 → Mat3,ContDiff ℝ (↑(⊤:ℕ∞)) H ∧ HasCompactSupport H ∧
    tsupport H⊆U ∧ (∀ x,(H x).IsSymm) ∧ ∀ j,symmetricSource H u j=r j

lemma symmetricSource_eq_of_weak
    {u : Coord3 → Fin 2 → ℝ} (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u)
    {H : Coord3 → Mat3} (hH : ContDiff ℝ (↑(⊤:ℕ∞)) H) (hc : HasCompactSupport H)
    {r : PhysicalSourcePair} (hr : CompactSmoothPair r)
    (hw : ∀ j (ψ : Coord3 → ℝ),ContDiff ℝ (↑(⊤:ℕ∞)) ψ →
      (∫ x,fderiv ℝ ψ x ((H x*gradientColumns (fderiv ℝ u x)).col j))=-(∫ x,ψ x*r j x)) :
    ∀ j,symmetricSource H u j=r j := by
  intro j
  have hs := coordinateDivergence_smooth (symmetricFlux_smooth hH hu j)
  apply Measure.eq_of_ae_eq (μ := volume) _ hs.continuous (hr j).1.continuous
  apply ae_eq_of_integral_contDiff_smul_eq hs.continuous.locallyIntegrable
    (hr j).1.continuous.locallyIntegrable
  intro ψ hψ _
  have he := coordinateDivergence_weak (symmetricFlux_smooth hH hu j)
    (symmetricFlux_compact hc u j) ψ hψ
  have he' := hw j ψ hψ
  simp only [smul_eq_mul]
  change (∫ x,ψ x*coordinateDivergence (fun x => (H x*gradientColumns (fderiv ℝ u x)).col j) x)=_
  linarith

lemma coordinateDivergence_add {F G : Coord3 → Coord3}
    (hF : ContDiff ℝ (↑(⊤:ℕ∞)) F) (hG : ContDiff ℝ (↑(⊤:ℕ∞)) G) :
    coordinateDivergence (F+G)=coordinateDivergence F+coordinateDivergence G := by
  funext x
  simp only [coordinateDivergence,Pi.add_apply,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have he := (((contDiff_pi.mp hF i).differentiable (by simp) x).hasFDerivAt.add
    ((contDiff_pi.mp hG i).differentiable (by simp) x).hasFDerivAt).fderiv
  exact congrArg (fun D : Coord3 →L[ℝ] ℝ => D (Pi.single i 1)) he

lemma symmetricSource_add {H K : Coord3 → Mat3} {u : Coord3 → Fin 2 → ℝ}
    (hH : ContDiff ℝ (↑(⊤:ℕ∞)) H) (hK : ContDiff ℝ (↑(⊤:ℕ∞)) K)
    (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u) (j : Fin 2) :
    symmetricSource (H+K) u j=symmetricSource H u j+symmetricSource K u j := by
  have he : (fun x => ((H+K) x*gradientColumns (fderiv ℝ u x)).col j)=
      (fun x => (H x*gradientColumns (fderiv ℝ u x)).col j)+
        (fun x => (K x*gradientColumns (fderiv ℝ u x)).col j) := by
    funext x i
    simp [Matrix.add_mul]
  unfold symmetricSource
  rw [he,coordinateDivergence_add (symmetricFlux_smooth hH hu j) (symmetricFlux_smooth hK hu j)]

namespace PhysicallyCorrectable
variable {u : Coord3 → Fin 2 → ℝ} {U : Set Coord3} {r s : PhysicalSourcePair}
lemma zero : PhysicallyCorrectable u U 0 := by
  refine ⟨0,contDiff_const,HasCompactSupport.zero,by simp [tsupport_zero],fun _ => Matrix.isSymm_zero,?_⟩
  intro j
  funext x
  simp [symmetricSource,coordinateDivergence,Matrix.col]
lemma add (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u)
    (hr : PhysicallyCorrectable u U r) (hs : PhysicallyCorrectable u U s) :
    PhysicallyCorrectable u U (r+s) := by
  obtain ⟨H,hH,hHc,hHs,hHsy,hHr⟩ := hr
  obtain ⟨K,hK,hKc,hKs,hKsy,hKr⟩ := hs
  refine ⟨H+K,hH.add hK,hHc.add hKc,(tsupport_add H K).trans (union_subset hHs hKs),
    fun x => (hHsy x).add (hKsy x),?_⟩
  intro j
  rw [symmetricSource_add hH hK hu j,hHr j,hKr j]
  rfl
end PhysicallyCorrectable

lemma RegularCorrectionBox.correct
    {u : Coord3 → Fin 2 → ℝ} (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u) {U : Set Coord3}
    (B : RegularCorrectionBox u U) {r : PhysicalSourcePair}
    (hr : CompactSmoothPair r) (hs : PairSupported r B.region)
    (hm : physicalSourceMoment u r=0) : PhysicallyCorrectable u U r := by
  have hz (j : Fin 2) : (∫ x,r j x)=0 := by
    fin_cases j
    · exact congrFun hm 0
    · exact congrFun hm 1
  have ht : (∫ x,u x 1*r 0 x-u x 0*r 1 x)=0 := congrFun hm 2
  obtain ⟨H,hH,hc,hsub,hsy,hw⟩ := local_physical_symmetric_correction B.chart B.smooth
    B.inverse_smooth B.widths B.subset_source u B.potentials r
    (fun j => (hr j).1) (fun j => (hr j).2) hs hz ht
  exact ⟨H,hH,hc,hsub.trans B.target_subset,hsy,symmetricSource_eq_of_weak hu hH hc hr hw⟩

end ScalarConductivity

end

end OAI
