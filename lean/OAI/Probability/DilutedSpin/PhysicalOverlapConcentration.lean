import OAI.Probability.DilutedSpin.MarkerScheduledIdentity
import OAI.Probability.DilutedSpin.RegularOverlapGeometry

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory _root_.OAI.MeasureTheory
noncomputable local instance physicalOverlapConcentrationTreeDecidableEq (type : Type) :
    DecidableEq type := Classical.decEq type
variable {Z : Type} [MeasurableSpace Z] {h h' N k : ℕ}

lemma markerMatrixCovariance_uncast (e : h=h')
    (μ : Measure Z) (Ω : Z → Type) [∀ z, Fintype (Ω z)]
    (S : PrescribedTree h) (a : S.Leaf) (T : PrescribedTree h) (q : Option (Fin k) → T.Leaf)
    (K : (z : Z) → KernelTower (Ω z) h') (m : Fin (h'+1) → ℝ)
    (V : (z : Z) → FinitePath (Ω z) h' → Fin N → ℝ) :
    markerMatrixCovariance μ Ω (heightCast e S) (leafHeightCast e S a)
      (heightCast e T) (fun c => leafHeightCast e T (q c)) K m V =
    markerMatrixCovariance μ Ω S a T q (fun z => kernelHeightCast e.symm (K z))
      (fun j => m (Fin.cast (congrArg (fun a => a+1) e) j))
      (fun z => vectorHeightCast e.symm (V z)) := by cases e; rfl

end DilutedSpinGlass.PrescribedTree
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir
open ReducedTopology Filter Set
open scoped NNReal BigOperators Topology
noncomputable local instance physicalOverlapConcentrationDictionaryDecidableEq (type : Type) :
    DecidableEq type := Classical.decEq type
variable {L p : ℕ}

noncomputable def physicalOverlapVariance (M : Model p) (C H : ℝ) (N L : ℕ)
    (u : Spec L×ℕ → ℝ) (S : ReducedTopology) (q : S.Vertex → Fin (L+1)) : ℝ :=
  scheduledOverlapVariance
    (fullRootLaw (fun _ : Fin N => M.field.toMeasure) (bondLaw M N)
      (markLaw (weights L) N) (M.alpha*N) (scoreRate N))
    (rootAlphabet (Ω := Fin N → Spin) (A := fun i : Labels L (Site N) => Alphabet i.1.1)) S (fun v => (q v).val)
    (rootTower (KernelTower.terminalTower (fun _ : Fin N => false) FiniteLaw.uniform L)
      (fun i => prior i.1.1) (gridExponents L) (physicalBase M C H N)
      (dictionaryFactor (observableAt direction N) (observableAt anchor N) u))
    (rootVector (readVector (fun v x => readSpin (KernelTower.terminalState L x) v)))

noncomputable def physicalMarkerDefect (M : Model p) (C H : ℝ) (N L : ℕ)
    (u : Spec L×ℕ → ℝ) (S : ReducedTopology) (Q : Option S.Vertex → Fin (L+1)) : ℝ :=
  scheduledMarkerDefect
    (fullRootLaw (fun _ : Fin N => M.field.toMeasure) (bondLaw M N)
      (markLaw (weights L) N) (M.alpha*N) (scoreRate N))
    (rootAlphabet (Ω := Fin N → Spin) (A := fun i : Labels L (Site N) => Alphabet i.1.1))
    (Q none).val S (fun v => (Q (some v)).val)
    (rootTower (KernelTower.terminalTower (fun _ : Fin N => false) FiniteLaw.uniform L)
      (fun i => prior i.1.1) (gridExponents L) (physicalBase M C H N)
      (dictionaryFactor (observableAt direction N) (observableAt anchor N) u))
    (rootVector (readVector (fun v x => readSpin (KernelTower.terminalState L x) v)))

lemma FullShapeControl.markerDefect {M : Model p} {C H : ℝ}
    {Ns : ℕ → ℕ} {us : ℕ → Spec L×ℕ → ℝ} (h : FullShapeControl M C H L Ns us)
    (S : ReducedTopology) (Q : Option S.Vertex → Fin (L+1)) :
    Tendsto (fun t => physicalMarkerDefect M C H (Ns t+1) L (us t) S Q) atTop (𝓝 0) := by
  let d := (Q none).val
  let n := L-d
  have e : L+1=n+1+d := by dsimp [n,d]; have := (Q none).isLt; omega
  let A := realize n (d+1) S (fun v => (Q (some v)).val)
  let S' := stem (unary A) d
  let T' := stem (markerFork A) d
  let a := firstLeaf S'
  let q := markerColorTarget A d
  let m : Fin (n+1+d+1) → ℝ := fun j =>
    (Fin.cons 0 (gridExponents L) : Fin (L+2) → ℝ) (Fin.cast (congrArg (fun a => a+1) e.symm) j)
  let κ := partialKappa T' m (Finset.univ.image q)
  have hm : StrictMono m := by
    intro i j hij
    dsimp [m]
    rw [gridExponents_cons]
    apply (grid_strictMono (by omega : 0<L+1))
    simpa only [Fin.cast_lt_cast] using hij
  have hp : ∀ j, 0 ≤ m j := by
    intro j
    dsimp [m]
    rw [gridExponents_cons]
    exact grid_nonneg _
  have hend : m (Fin.last (n+1+d))=1 := by
    dsimp [m]
    simp only [Fin.cast_last]
    rw [gridExponents_cons]
    exact grid_last (by omega)
  have hκ : κ≠0 := partialKappa_ne_zero T' m hm hp _
  have hcard : 0<Fintype.card A.Leaf := by
    have : Nonempty A.Leaf := ⟨firstLeaf A⟩
    exact Fintype.card_pos
  have ht := h.marker (heightCast e.symm S') (leafHeightCast e.symm S' a)
    (Fintype.card A.Leaf) hcard (heightCast e.symm T') (fun c => leafHeightCast e.symm T' (q c))
  have heq (t : ℕ) : physicalMarkerMatrixCovariance (gridExponents L)
      (heightCast e.symm S') (leafHeightCast e.symm S' a) M C H (Ns t+1) (us t)
      (heightCast e.symm T') (fun c => leafHeightCast e.symm T' (q c)) =
      κ * physicalMarkerDefect M C H (Ns t+1) L (us t) S Q := by
    unfold physicalMarkerMatrixCovariance physicalMarkerDefect
    exact scheduledMarkerDefect_covariance _ _ n d S _ e _ (Fin.cons 0 (gridExponents L))
      (by rw [gridExponents_cons]; exact grid_strictMono (by omega))
      (by rw [gridExponents_cons]; exact grid_nonneg)
      (by rw [gridExponents_cons]; exact grid_last (by omega)) _
  have hx : Tendsto (fun t => κ*physicalMarkerDefect M C H (Ns t+1) L (us t) S Q) atTop (𝓝 0) := by
    simpa only [heq] using ht
  have hh := hx.div_const κ
  simpa only [mul_div_cancel_left₀ _ hκ,zero_div] using hh

lemma physicalOverlapVariance_le_marker (M : Model p) (C H : ℝ) (N L : ℕ)
    (u : Spec L×ℕ → ℝ) (S : ReducedTopology) (Q : Option S.Vertex → Fin (L+1))
    (hq : ∀ v, (Q none).val+1≤(Q (some v)).val) :
    physicalOverlapVariance M C H N L u S (fun v => Q (some v)) ≤
      Real.sqrt (physicalScheduledEnergy M C H N L u S Q)+|physicalMarkerDefect M C H N L u S Q| := by
  unfold physicalOverlapVariance physicalScheduledEnergy physicalMarkerDefect
  exact root_scheduled_variance_le_marker _ _ _ _ _ _ (measurable_physicalBase M C H N) _
    (fun y i => readVector_bound _ y i) (L-(Q none).val) (Q none).val S _
    (by have := (Q none).isLt; omega) hq

end DilutedSpinGlass.UniversalDictionary

end

section
namespace DilutedSpinGlass.DepthAverage
open scoped BigOperators
noncomputable local instance physicalOverlapConcentrationAverageDecidableEq (type : Type) :
    DecidableEq type := Classical.decEq type
noncomputable local instance physicalOverlapConcentrationAverageDecidable (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition
variable {α : Type} [Fintype α] [DecidableEq α] {L : ℕ} [NeZero L]

lemma average_domain_bound (D E : (α → Fin L) → Prop) (F G : (α → Fin L) → ℝ)
    (hDE : ∀ q, D q → E q) (hFG : ∀ q, D q → F q≤G q) (hG : ∀ q, 0≤G q) :
    average D F≤average E G := by
  apply FiniteLaw.expect_mono
  intro q
  by_cases hd : D q
  · rw [ite_eq_left hd,ite_eq_left (hDE q hd)]
    exact hFG q hd
  · rw [ite_eq_right hd]
    split_ifs
    · exact hG q
    · rfl

lemma average_option_interval_bound (r : ℕ) (hr : 2*r<L) (c : ℝ) (hc : c≤(r:ℝ)/(L:ℝ))
    (A : (α → Fin L) → Prop) (B : (Option α → Fin L) → Prop)
    (F : (α → Fin L) → ℝ) (E D : (Option α → Fin L) → ℝ)
    (hF : ∀ q, 0≤F q) (hE : ∀ Q, 0≤E Q) (hD : ∀ Q, 0≤D Q)
    (hsub : ∀ Q, A (fun v => Q (some v)) ∧ r<(Q none).val ∧ (Q none).val≤2*r → B Q)
    (hpoint : ∀ Q, B Q → F (fun v => Q (some v))≤Real.sqrt (E Q)+D Q) :
    c*average A F≤Real.sqrt (average B E)+average B D := by
  let I := fun Q : Option α → Fin L => A (fun v => Q (some v)) ∧ r<(Q none).val ∧ (Q none).val≤2*r
  have hav : average I (fun Q => F (fun v => Q (some v)))=((r:ℝ)/(L:ℝ))*average A F := by
    have hh := average_option_product A (fun t : Fin L => r<t.val ∧ t.val≤2*r) F
    calc
      _ = _ := hh
      _ = _ := congrArg (fun x : ℝ => x*average A F) (by
        convert uniform_interval r hr using 1
        apply FiniteLaw.expect_congr
        intro t
        split_ifs <;> rfl)
  calc
    _ ≤ ((r:ℝ)/(L:ℝ))*average A F := mul_le_mul_of_nonneg_right hc (average_nonneg _ _ hF)
    _ = average I (fun Q => F (fun v => Q (some v))) := hav.symm
    _ ≤ average B (fun Q => Real.sqrt (E Q)+D Q) :=
      average_domain_bound I B _ _ hsub (fun Q hQ => hpoint Q (hsub Q hQ))
        (fun Q => add_nonneg (Real.sqrt_nonneg _) (hD Q))
    _ = average B (fun Q => Real.sqrt (E Q))+average B D := average_add_eq _ _ _
    _ ≤ _ := add_le_add (average_sqrt_le B E hE) le_rfl

end DilutedSpinGlass.DepthAverage
namespace DilutedSpinGlass.ReducedTopology
open DepthAverage
open scoped BigOperators
noncomputable local instance physicalOverlapConcentrationTopologyDecidableEq (type : Type) :
    DecidableEq type := Classical.decEq type
noncomputable local instance physicalOverlapConcentrationTopologyDecidable (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition
variable {L : ℕ} [NeZero L]

/-- A positive fraction of early marker prefixes transfers the covariance
estimate without a mesh-size penalty or a diagonal depth restriction. -/
theorem regular_overlap_average_bound (S : ReducedTopology) {η : ℝ}
    (hη : 0<η) (hη1 : η≤1) (hlarge : 8<η*(L:ℝ))
    (F : (S.Vertex → Fin L) → ℝ) (E D : (Option S.Vertex → Fin L) → ℝ)
    (hF : ∀ q, 0≤F q) (hE : ∀ Q, 0≤E Q) (hD : ∀ Q, 0≤D Q)
    (hpoint : ∀ Q, regularShapeDomain S L (η/8) Q →
      F (fun v => Q (some v))≤Real.sqrt (E Q)+D Q) :
    (η/8)*average (regularOverlapDomain S L η) F ≤
      Real.sqrt (average (regularShapeDomain S L (η/8)) E)+
      average (regularShapeDomain S L (η/8)) D := by
  have hg := overlap_interval_geometry hη hη1 hlarge
  apply average_option_interval_bound _ hg.1 _ hg.2.1
    (regularOverlapDomain S L η) (regularShapeDomain S L (η/8)) F E D hF hE hD _ hpoint
  intro Q hQ
  have hd := hg.2.2 (Q none) hQ.2
  have hh := regularOverlap_prepend hη hη1 S (fun v => Q (some v)) hQ.1 (Q none) hd.1 hd.2
  have he : (fun i : Option S.Vertex => i.elim (Q none) (fun v => Q (some v)))=Q := by
    funext i; cases i <;> rfl
  rwa [he] at hh

end DilutedSpinGlass.ReducedTopology

end

end OAI
