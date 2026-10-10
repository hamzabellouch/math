import Mathlib
import OAI.Analysis.Conductivity.Branching.ParametricCorrectionTransport
import OAI.Analysis.Conductivity.Sources.ParametricSymmetricSources
import OAI.Analysis.Conductivity.Variational.SmoothPhysicalMomentFamily

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

def SmoothVanishingPairFamily (p : P) (W : Set Coord3)
    (r : Fin 2 → P×Coord3 → ℝ) : Prop :=
  (∀ j,ContDiff ℝ (↑(⊤:ℕ∞)) (r j)) ∧ (∀ j x,r j (p,x)=0) ∧
    ∃ K : Set Coord3,IsCompact K ∧ K⊆W ∧ ∀ q,PairSupported (fun j x => r j (q,x)) K

namespace SmoothVanishingPairFamily
omit [FiniteDimensional ℝ P]
variable {p : P} {W V : Set Coord3} {r s : Fin 2 → P×Coord3 → ℝ}
lemma mono (hr : SmoothVanishingPairFamily p W r) (hWV : W⊆V) :
    SmoothVanishingPairFamily p V r := by
  obtain ⟨hsm,hz,K,hK,hKW,hs⟩ := hr
  exact ⟨hsm,hz,K,hK,hKW.trans hWV,hs⟩
lemma compact (hr : SmoothVanishingPairFamily p W r) (q : P) :
    CompactSmoothPair (fun j x => r j (q,x)) := by
  obtain ⟨hsm,_,K,hK,_,hs⟩ := hr
  exact fun j => ⟨(hsm j).comp (contDiff_const.prodMk contDiff_id),
    hK.of_isClosed_subset (isClosed_tsupport _) (hs q j)⟩
lemma supported (hr : SmoothVanishingPairFamily p W r) (q : P) :
    PairSupported (fun j x => r j (q,x)) W := by
  obtain ⟨_,_,K,_,hKW,hs⟩ := hr
  exact (hs q).mono hKW
lemma sub (hr : SmoothVanishingPairFamily p W r) (hs : SmoothVanishingPairFamily p W s) :
    SmoothVanishingPairFamily p W (r-s) := by
  obtain ⟨hr,hrz,K,hK,hKW,hKr⟩ := hr
  obtain ⟨hs,hsz,L,hL,hLW,hLs⟩ := hs
  exact ⟨fun j => (hr j).sub (hs j),fun j x => by simp [hrz,hsz],
    K∪L,hK.union hL,union_subset hKW hLW,fun q =>
      ((hKr q).mono subset_union_left).sub ((hLs q).mono subset_union_right)⟩
end SmoothVanishingPairFamily

structure VanishingCorrectionRegion (u : P×Coord3 → Fin 2 → ℝ) (p : P) (U : Set Coord3) where
  region : Set Coord3
  region_open : IsOpen region
  region_nonempty : region.Nonempty
  region_subset : region⊆U
  region_bounded : Bornology.IsBounded region
  solve : ∀ (r : Fin 2 → P×Coord3 → ℝ),SmoothVanishingPairFamily p region r →
    ∀ ε : ℝ,0<ε → ∀ᶠ q in 𝓝 p,
      physicalSourceMoment (fun x => u (q,x)) (fun j x => r j (q,x))=0 →
      BoundedPhysicallyCorrectable (fun x => u (q,x)) U (fun j x => r j (q,x)) ε

def ParametricCorrectionBox.toVanishing
    {u : P×Coord3 → Fin 2 → ℝ} (p : P) {U : Set Coord3}
    (B : ParametricCorrectionBox u p U) : VanishingCorrectionRegion u p U := by
  refine ⟨B.region,B.region_open,B.region_nonempty,B.region_subset,B.region_bounded,?_⟩
  intro r hr ε hε
  obtain ⟨L,hL,solve⟩ := B.bounded_solver
  obtain ⟨hsm,hz,K,hK,hKW,hs⟩ := hr
  have hsmall (j) := compact_supported_family_C1_small isOpen_univ (mem_univ p)
    (hsm j).contDiffOn hK (Filter.Eventually.of_forall (fun q => hs q j)) (hz j) (div_pos hε hL)
  filter_upwards [solve,Filter.eventually_all.mpr hsmall] with q hq hb hm
  have hrs : CompactSmoothPair (fun j x => r j (q,x)) :=
    SmoothVanishingPairFamily.compact ⟨hsm,hz,K,hK,hKW,hs⟩ q
  have h := hq _ hrs ((hs q).mono hKW) hm (ε/L) (div_pos hε hL).le hb
  simpa only [mul_div_cancel₀ ε hL.ne'] using h

theorem VanishingCorrectionRegion.smooth_transfer
    {u : P×Coord3 → Fin 2 → ℝ} (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u) (p : P) {U : Set Coord3}
    (B C : VanishingCorrectionRegion u p U) {x : Coord3}
    (hx : x∈B.region∩C.region)
    (hD : Function.Surjective (fderiv ℝ (fun y => u (p,y)) x))
    {r : Fin 2 → P×Coord3 → ℝ} (hr : SmoothVanishingPairFamily p B.region r) :
    ∃ s : Fin 2 → P×Coord3 → ℝ,SmoothVanishingPairFamily p C.region s ∧
      (∀ᶠ q in 𝓝 p,physicalSourceMoment (fun y => u (q,y)) (fun j y => s j (q,y))=
        physicalSourceMoment (fun y => u (q,y)) (fun j y => r j (q,y))) ∧
      ∀ ε : ℝ,0<ε → ∀ᶠ q in 𝓝 p,
        BoundedPhysicallyCorrectable (fun y => u (q,y)) U
          ((fun j y => r j (q,y))-(fun j y => s j (q,y))) ε := by
  obtain ⟨K,hK,hKW,hs⟩ := hr.2.2
  let m : P → Coord3 := fun q => physicalSourceMoment (fun y => u (q,y)) (fun j y => r j (q,y))
  have hm : ContDiff ℝ (↑(⊤:ℕ∞)) m := physicalSourceMoment_family_smooth hu hr.1 hK hs
  have hmz : m p=0 := by
    change physicalSourceMoment (fun y => u (p,y)) (fun j y => r j (p,y))=0
    rw [show (fun j y => r j (p,y))=0 by funext j y; exact hr.2.1 j y,physicalSourceMoment_zero]
  obtain ⟨L,hL,hLO,s,hsm,hss,hsz,hsmom⟩ := smooth_physical_moment_family hu p
    (B.region_open.inter C.region_open) hx hD hm hmz
  have hsf : SmoothVanishingPairFamily p (B.region∩C.region) s := ⟨hsm,hsz,L,hL,hLO,hss⟩
  refine ⟨s,hsf.mono inter_subset_right,hsmom,?_⟩
  intro ε hε
  have hsolve := B.solve (r-s) (hr.sub (hsf.mono inter_subset_left)) ε hε
  filter_upwards [hsolve,hsmom] with q solve mom
  apply solve
  have huq : ContDiff ℝ (↑(⊤:ℕ∞)) (fun y => u (q,y)) := hu.comp (contDiff_const.prodMk contDiff_id)
  change physicalSourceMoment (fun y => u (q,y))
    ((fun j y => r j (q,y))-(fun j y => s j (q,y)))=0
  rw [physicalSourceMoment_sub huq.continuous (hr.compact q) (hsf.compact q),mom,sub_self]

theorem smooth_chain_source_transport
    {u : P×Coord3 → Fin 2 → ℝ} (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u) (p : P) {U : Set Coord3}
    {B C : VanishingCorrectionRegion u p U}
    (hpath : Relation.TransGen (fun B C : VanishingCorrectionRegion u p U =>
      ∃ x∈B.region∩C.region,Function.Surjective (fderiv ℝ (fun y => u (p,y)) x)) B C) :
    ∀ {r : Fin 2 → P×Coord3 → ℝ},SmoothVanishingPairFamily p B.region r →
    ∃ s : Fin 2 → P×Coord3 → ℝ,SmoothVanishingPairFamily p C.region s ∧
      (∀ᶠ q in 𝓝 p,physicalSourceMoment (fun y => u (q,y)) (fun j y => s j (q,y))=
        physicalSourceMoment (fun y => u (q,y)) (fun j y => r j (q,y))) ∧
      ∀ ε : ℝ,0<ε → ∀ᶠ q in 𝓝 p,
        BoundedPhysicallyCorrectable (fun y => u (q,y)) U
          ((fun j y => r j (q,y))-(fun j y => s j (q,y))) ε := by
  induction hpath with
  | @single C h =>
    obtain ⟨x,hx,hD⟩ := h
    exact fun hr => B.smooth_transfer hu p C hx hD hr
  | @tail C D hpath hCD ih =>
    intro r hr
    obtain ⟨s,hs,hsm,hsc⟩ := ih hr
    obtain ⟨x,hx,hD⟩ := hCD
    obtain ⟨t,ht,htm,htc⟩ := C.smooth_transfer hu p D hx hD hs
    refine ⟨t,ht,?_,?_⟩
    · filter_upwards [hsm,htm] with q hq htq
      exact htq.trans hq
    · intro ε hε
      filter_upwards [hsc (ε/2) (by linarith),htc (ε/2) (by linarith)] with q hq htq
      have huq : ContDiff ℝ (↑(⊤:ℕ∞)) (fun y => u (q,y)) :=
        hu.comp (contDiff_const.prodMk contDiff_id)
      have h := hq.add huq htq
      rw [sub_add_sub_cancel] at h
      simpa only [add_halves] using h

end ScalarConductivity

end
end

end OAI
