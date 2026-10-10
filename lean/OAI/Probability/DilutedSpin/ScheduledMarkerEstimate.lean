import OAI.Probability.DilutedSpin.PhysicalMarkerControl

namespace OAI

section
namespace DilutedSpinGlass.ReducedTopology
open _root_.MeasureTheory _root_.OAI.MeasureTheory PrescribedTree
variable {Z : Type} [MeasurableSpace Z] {L N : ℕ}

@[simp] lemma realize_heightCast {n m : ℕ} (e : n=m) (d : ℕ)
    (S : ReducedTopology) (q : S.Vertex → ℕ) :
    heightCast e (realize n d S q)=realize m d S q := by cases e; rfl

lemma realize_marker_form (n d : ℕ) (S : ReducedTopology) (q : S.Vertex → ℕ)
    (hq : ∀ v, d+1 ≤ q v) :
    realize (n+1+d) 0 S q = stem (unary (realize n (d+1) S q)) d := by
  rw [realize_stem (n+1) d 0 S q (fun v => by simpa using (hq v).trans' (Nat.le_succ d))]
  simp only [Nat.zero_add]
  rw [realize_unary_of_later n d S q (fun v => by have := hq v; omega)]

noncomputable def scheduledOverlapVariance (μ : Measure Z) (Ω : Z → Type) [∀ z, Fintype (Ω z)]
    (S : ReducedTopology) (q : S.Vertex → ℕ) (K : (z : Z) → KernelTower (Ω z) L)
    (V : (z : Z) → FinitePath (Ω z) L → Fin N → ℝ) : ℝ :=
  overlapVariance μ Ω (realize L 0 S q) K V

noncomputable def scheduledMarkerDefect (μ : Measure Z) (Ω : Z → Type) [∀ z, Fintype (Ω z)]
    (d : ℕ) (S : ReducedTopology) (q : S.Vertex → ℕ) (K : (z : Z) → KernelTower (Ω z) L)
    (V : (z : Z) → FinitePath (Ω z) L → Fin N → ℝ) : ℝ :=
  if h : d<L then markerDefect μ Ω (realize (L-(d+1)) (d+1) S q) d
    (fun z => kernelHeightCast (by omega) (K z)) (fun z => vectorHeightCast (by omega) (V z)) else 0

lemma scheduledMarkerDefect_eq_realize (μ : Measure Z) (Ω : Z → Type) [∀ z, Fintype (Ω z)]
    (n d : ℕ) (S : ReducedTopology) (q : S.Vertex → ℕ) (e : L=n+1+d)
    (K : (z : Z) → KernelTower (Ω z) L)
    (V : (z : Z) → FinitePath (Ω z) L → Fin N → ℝ) :
    scheduledMarkerDefect μ Ω d S q K V = markerDefect μ Ω (realize n (d+1) S q) d
      (fun z => kernelHeightCast e (K z)) (fun z => vectorHeightCast e (V z)) := by
  subst L
  unfold scheduledMarkerDefect
  rw [dite_eq_left (by omega : d<n+1+d)]
  have he (n' : ℕ) (hn : n'=n) (hc : n+1+d=n'+1+d) :
      markerDefect μ Ω (realize n' (d+1) S q) d
        (fun z => kernelHeightCast hc (K z)) (fun z => vectorHeightCast hc (V z)) =
      markerDefect μ Ω (realize n (d+1) S q) d K V := by
    subst n'
    rfl
  exact he _ (by omega) _

lemma scheduledOverlapVariance_eq_realize (μ : Measure Z) (Ω : Z → Type) [∀ z, Fintype (Ω z)]
    (n d : ℕ) (S : ReducedTopology) (q : S.Vertex → ℕ) (e : L=n+1+d)
    (hq : ∀ v, d+1≤q v) (K : (z : Z) → KernelTower (Ω z) L)
    (V : (z : Z) → FinitePath (Ω z) L → Fin N → ℝ) :
    scheduledOverlapVariance μ Ω S q K V =
      overlapVariance μ Ω (stem (unary (realize n (d+1) S q)) d)
        (fun z => kernelHeightCast e (K z)) (fun z => vectorHeightCast e (V z)) := by
  subst L
  unfold scheduledOverlapVariance
  rw [realize_marker_form n d S q hq]
  rfl

end DilutedSpinGlass.ReducedTopology
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory PrescribedTree ReducedTopology
open scoped NNReal BigOperators
variable {Ω I X Y : Type} [Fintype Ω] {B : I → Type} [∀ i, Fintype (B i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M N : ℕ}

variable (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (B i))
    (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (old : (i : I) → FinitePath Ω L → FinitePath (B i) L → ℝ)
    (V : FinitePath Ω L → Fin N → ℝ)
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
    (μ : Measure (FullRootState Y X I M)) [IsProbabilityMeasure μ]
    (hV : ∀ y i, |V y i| ≤ 1)

include hb hV in
lemma root_scheduled_variance_le_marker (n d : ℕ) (S : ReducedTopology) (q : S.Vertex → ℕ)
    (e : L=n+1+d) (hq : ∀ v, d+1≤q v) :
    scheduledOverlapVariance μ (rootAlphabet (Ω := Ω) (A := B)) S q
      (rootTower T Q m base old) (rootVector V) ≤
      Real.sqrt (∫ z, scheduledShapeEnergy L d S q (rootTower T Q m base old z) (rootVector V z) ∂μ) +
      |scheduledMarkerDefect μ (rootAlphabet (Ω := Ω) (A := B)) d S q
        (rootTower T Q m base old) (rootVector V)| := by
  subst L
  rw [scheduledOverlapVariance_eq_realize μ _ n d S q rfl hq,
    scheduledMarkerDefect_eq_realize μ _ n d S q rfl]
  simp_rw [scheduledShapeEnergy_eq_realize n d S q rfl]
  exact root_overlapVariance_le_marker (realize n (d+1) S q) T Q m base old V hb μ hV

end DilutedSpinGlass.HeterogeneousMarks

end

end OAI
