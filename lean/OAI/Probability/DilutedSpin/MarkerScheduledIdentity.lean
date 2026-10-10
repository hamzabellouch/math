import OAI.Probability.DilutedSpin.ScheduledMarkerEstimate

namespace OAI

section
namespace DilutedSpinGlass.ReducedTopology
open _root_.MeasureTheory _root_.OAI.MeasureTheory PrescribedTree
noncomputable local instance markerScheduledIdentityDecidableEq (carrier : Type) :
    DecidableEq carrier := Classical.decEq carrier
variable {Z : Type} [MeasurableSpace Z] {L N : ℕ}

lemma scheduledMarkerDefect_covariance (μ : Measure Z) (Ω : Z → Type) [∀ z, Fintype (Ω z)]
    (n d : ℕ) (S : ReducedTopology) (q : S.Vertex → ℕ) (e : L=n+1+d)
    (K : (z : Z) → KernelTower (Ω z) L) (m : Fin (L+1) → ℝ)
    (hm : StrictMono m) (hp : ∀ j, 0 ≤ m j) (hend : m (Fin.last L)=1)
    (V : (z : Z) → FinitePath (Ω z) L → Fin N → ℝ) :
    let A := realize n (d+1) S q
    let S' := stem (unary A) d
    let T' := stem (markerFork A) d
    let a := firstLeaf S'
    let q' := markerColorTarget A d
    markerMatrixCovariance μ Ω (heightCast e.symm S') (leafHeightCast e.symm S' a)
      (heightCast e.symm T') (fun c => leafHeightCast e.symm T' (q' c)) K m V =
      partialKappa T' (fun j => m (Fin.cast (congrArg (fun a => a+1) e.symm) j))
        (Finset.univ.image q') * scheduledMarkerDefect μ Ω d S q K V := by
  subst L
  dsimp only [heightCast,leafHeightCast,Fin.cast]
  rw [scheduledMarkerDefect_eq_realize μ Ω n d S q rfl]
  unfold markerMatrixCovariance
  convert concrete_marker_covariance_eq_defect μ Ω (realize n (d+1) S q) d
      (firstLeaf (stem (unary (realize n (d+1) S q)) d)) K m hm hp hend V using 1 <;> congr 3
  funext z x
  unfold spatialProduct
  congr 2
  funext i
  apply Finset.prod_congr rfl
  intro color _
  cases color <;> rfl

end DilutedSpinGlass.ReducedTopology

end

end OAI
