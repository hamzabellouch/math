import Mathlib
import OAI.Probability.SKFluctuations.ReplicaCovarianceVariation

namespace OAI

/-! Replica Mixed Insertion. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators
variable {S : Type*} [Fintype S] [Nonempty S] {n : ℕ}
namespace ClockPolynomial
variable {as : List PositiveMass}

 

def lowJet (E : ClockExpr S as) (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ)
    (d₀ e₀ : Fin (n+1) → ℝ) (d e : ℕ → Fin (n+1) → ℝ) : ℕ → ClockPolynomial S as
  | 0 => [(1,E)]
  | k+1 => (lowJet E φ d₀ e₀ d e k).affineInsert φ d₀ e₀ d e

 theorem iteratedDeriv_lowJet {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) (E : ClockExpr S as)
    {a : ℝ} (ho : MassOrdered a as) (q₀ d₀ e₀ : Fin (n+1) → ℝ)
    (q d e : ℕ → Fin (n+1) → ℝ) {l r : ℝ} (t : ℝ)
    (hp : ∀ j, ∀ s ∈ Ioo l r, ∀ i, 0 ≤ q j i+s*(d j i+t*e j i))
    (hr : ∀ s ∈ Ioo l r, ∀ i, 0 ≤ q₀ i+s*(d₀ i+t*e₀ i))
    (x : Fin (n+1) → ℝ) (k : ℕ) {u : ℝ} (hu : u ∈ Ioo l r) :
    iteratedDeriv k (fun s => E.rootEval w φ (fun i => q₀ i+s*(d₀ i+t*e₀ i))
      (fun j i => q j i+s*(d j i+t*e j i)) x) u =
      (lowJet E φ d₀ e₀ d e k).rootEval w φ t (fun i => q₀ i+u*(d₀ i+t*e₀ i))
        (fun j i => q j i+u*(d j i+t*e j i)) x := by
  induction k generalizing u with
  | zero => simp [lowJet,rootEval]
  | succ k ih =>
    rw [iteratedDeriv_succ]
    have he : iteratedDeriv k (fun s => E.rootEval w φ (fun i => q₀ i+s*(d₀ i+t*e₀ i))
        (fun j i => q j i+s*(d j i+t*e j i)) x) =ᶠ[𝓝 u]
        (fun s => (lowJet E φ d₀ e₀ d e k).rootEval w φ t
          (fun i => q₀ i+s*(d₀ i+t*e₀ i)) (fun j i => q j i+s*(d j i+t*e j i)) x) := by
      filter_upwards [isOpen_Ioo.mem_nhds hu] with s hs
      exact ih hs
    rw [he.deriv_eq,lowJet,rootEval_affineInsert hw φ _ ho]
    exact ((lowJet E φ d₀ e₀ d e k).hasDerivAt_frozen hw φ ho q₀ _ q _ hp hr hu t x).deriv

 theorem rootEval_continuous {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) (P : ClockPolynomial S as)
    (q₀ : ℝ → Fin (n+1) → ℝ) (q : ℕ → ℝ → Fin (n+1) → ℝ)
    (hq₀ : Continuous q₀) (hq : ∀ j, Continuous (q j))
    (x : ℝ → Fin (n+1) → ℝ) (hx : Continuous x) :
    Continuous (fun t => P.rootEval w φ t (q₀ t) (fun j => q j t) (x t)) := by
  induction P with
  | nil => exact continuous_const
  | cons p P ih => exact (p.1.continuous.mul (p.2.rootEval_continuous hw φ q₀ q hq₀ hq x hx)).add ih

 

 theorem mixed_lowJet_hasDerivAt {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) (E : ClockExpr S as)
    {a : ℝ} (ho : MassOrdered a as) (q₀ b₀ c₀ d₀ : Fin (n+1) → ℝ)
    (q b c d : ℕ → Fin (n+1) → ℝ) {l₀ l₁ t₀ t₁ l t : ℝ}
    (hp : ∀ j, ∀ u ∈ Ioo l₀ l₁, ∀ s ∈ Ioo t₀ t₁, ∀ i,
      0 ≤ q j i+s*c j i+u*(b j i+s*d j i))
    (hr : ∀ u ∈ Ioo l₀ l₁, ∀ s ∈ Ioo t₀ t₁, ∀ i,
      0 ≤ q₀ i+s*c₀ i+u*(b₀ i+s*d₀ i))
    (hl : l ∈ Ioo l₀ l₁) (ht : t ∈ Ioo t₀ t₁) (x : Fin (n+1) → ℝ) (k : ℕ) :
    HasDerivAt (fun s => iteratedDeriv k (fun u => E.rootEval w φ
      (fun i => q₀ i+s*c₀ i+u*(b₀ i+s*d₀ i))
      (fun j i => q j i+s*c j i+u*(b j i+s*d j i)) x) l)
      (((lowJet E φ b₀ d₀ b d k).coeffDeriv ++
        (lowJet E φ b₀ d₀ b d k).insert φ (fun i => c₀ i+l*d₀ i)
          (fun j i => c j i+l*d j i)).rootEval w φ t
        (fun i => q₀ i+t*c₀ i+l*(b₀ i+t*d₀ i))
        (fun j i => q j i+t*c j i+l*(b j i+t*d j i)) x) t := by
  have hpin : ∀ j, ∀ s ∈ Ioo t₀ t₁, ∀ i,
      0 ≤ (q j i+l*b j i)+s*(c j i+l*d j i) := by
    intro j s hs i
    nlinarith [hp j l hl s hs i]
  have hrin : ∀ s ∈ Ioo t₀ t₁, ∀ i,
      0 ≤ (q₀ i+l*b₀ i)+s*(c₀ i+l*d₀ i) := by
    intro s hs i
    nlinarith [hr l hl s hs i]
  have h := (lowJet E φ b₀ d₀ b d k).hasDerivAt_diagonal hw φ ho
    (fun i => q₀ i+l*b₀ i) (fun i => c₀ i+l*d₀ i)
    (fun j i => q j i+l*b j i) (fun j i => c j i+l*d j i) hpin hrin ht x
  have he₀ (s : ℝ) : (fun i => q₀ i+l*b₀ i+s*(c₀ i+l*d₀ i)) =
      (fun i => q₀ i+s*c₀ i+l*(b₀ i+s*d₀ i)) := by funext i; ring
  have he (s : ℝ) : (fun j i => q j i+l*b j i+s*(c j i+l*d j i)) =
      (fun j i => q j i+s*c j i+l*(b j i+s*d j i)) := by funext j i; ring
  simp only [he₀,he] at h
  apply h.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
  exact iteratedDeriv_lowJet hw φ E ho (fun i => q₀ i+s*c₀ i) b₀ d₀
    (fun j i => q j i+s*c j i) b d s
    (fun j u hu i => hp j u hu s hs i) (fun u hu i => hr u hu s hs i) x k hl

end ClockPolynomial
end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators
variable {S : Type*} [Fintype S] [Nonempty S] {n : ℕ}

def ClockExpr.cumulativeEval (w : S → ℝ) (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ)
    {as : List PositiveMass} (E : ClockExpr S as) (v : Fin (n+1) → ℝ)
    (q : ℕ → Fin (n+1) → ℝ) (x : Fin (n+1) → ℝ) : ℝ :=
  E.rootEval w φ (fun i => q 0 i-v i) (fun j i => q (j+1) i-q j i) x

def ClockExpr.cumulativeCov (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ)
    {as : List PositiveMass} (E : ClockExpr S as) (d : ℕ → Fin (n+1) → ℝ) : ClockExpr S as :=
  E.rootCov φ (d 0) (fun j i => d (j+1) i-d j i)

def ClockExpr.iterCumulativeCov (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ)
    {as : List PositiveMass} (E : ClockExpr S as) (d : ℕ → Fin (n+1) → ℝ) (k : ℕ) : ClockExpr S as :=
  E.iterRootCov φ (d 0) (fun j i => d (j+1) i-d j i) k

omit [Nonempty S] in
 theorem ClockExpr.cumulativeEval_affine (w : S → ℝ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (E : ClockExpr S as)
    (v : Fin (n+1) → ℝ) (q d : ℕ → Fin (n+1) → ℝ) (t : ℝ) (x : Fin (n+1) → ℝ) :
    E.cumulativeEval w φ v (fun j i => q j i+t*d j i) x =
      E.rootEval w φ (fun i => q 0 i-v i+t*d 0 i)
        (fun j i => (q (j+1) i-q j i)+t*(d (j+1) i-d j i)) x := by
  unfold ClockExpr.cumulativeEval
  congr 1 <;> funext i
  · ring
  · funext s; ring

 

 theorem ClockTree.iteratedDeriv_disorderExpect {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (T : ClockTree S as)
    {a : ℝ} (ho : MassOrdered a as) (v : Fin (n+1) → ℝ)
    (q d : ℕ → Fin (n+1) → ℝ) {l r : ℝ}
    (hp : ∀ s ∈ Ioo l r, ∀ i, Monotone (fun j => q j i+s*d j i))
    (hr : ∀ s ∈ Ioo l r, ∀ i, v i ≤ q 0 i+s*d 0 i)
    (P : T.Assignment → ℝ) (x : Fin (n+1) → ℝ) (k : ℕ) {t : ℝ} (ht : t ∈ Ioo l r) :
    iteratedDeriv k (fun s => T.disorderExpect w φ v (fun j i => q j i+s*d j i) P x) t =
      ((T.testExpr P).iterCumulativeCov φ d k).cumulativeEval w φ v
        (fun j i => q j i+t*d j i) x := by
  have hinc : ∀ j, ∀ s ∈ Ioo l r, ∀ i,
      0 ≤ (q (j+1) i-q j i)+s*(d (j+1) i-d j i) := by
    intro j s hs i
    have h := hp s hs i (Nat.le_succ j)
    linarith
  have hroot : ∀ s ∈ Ioo l r, ∀ i, 0 ≤ q 0 i-v i+s*d 0 i := by
    intro s hs i
    linarith [hr s hs i]
  have he : (fun s => T.disorderExpect w φ v (fun j i => q j i+s*d j i) P x) =
      fun s => (T.testExpr P).rootEval w φ (fun i => q 0 i-v i+s*d 0 i)
        (fun j i => (q (j+1) i-q j i)+s*(d (j+1) i-d j i)) x := by
    funext s
    rw [← T.rootEval_testExpr hw φ ho]
    exact (ClockExpr.cumulativeEval_affine w φ (T.testExpr P) v q d s x)
  rw [he,ClockExpr.cumulativeEval_affine]
  exact (T.testExpr P).iteratedDeriv_rootEval hw φ ho (fun i => q 0 i-v i) (d 0)
    (fun j i => q (j+1) i-q j i) (fun j i => d (j+1) i-d j i) hinc hroot x k ht

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators
variable {S ι κ : Type*} [Fintype S] [Fintype ι] [Fintype κ]

 theorem ClockTree.disorderExpect_reindex (e : κ ≃ ι) (w : S → ℝ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (T : ClockTree S as)
    (v : ι → ℝ) (q : ℕ → ι → ℝ) (P : T.Assignment → ℝ) (x : κ → ℝ) :
    T.disorderExpect w (reindexFeature e φ) (fun i => v (e i)) (fun j i => q j (e i)) P x =
      T.disorderExpect w φ v q P (coordinateEquiv e x) := by
  simp only [ClockTree.disorderExpect,T.disorderWeight_reindex]

variable [Nonempty S] [Nonempty ι]

 
def ClockExpr.finiteCumulativeCov (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {as : List PositiveMass} (E : ClockExpr S as) (d : ℕ → ι → ℝ) (k : ℕ) : ClockExpr S as :=
  E.iterCumulativeCov (reindexFeature (finiteJetEquiv ι) φ)
    (fun j i => d j (finiteJetEquiv ι i)) k

def ClockExpr.finiteCumulativeEval (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {as : List PositiveMass} (E : ClockExpr S as) (v : ι → ℝ)
    (q : ℕ → ι → ℝ) (x : ι → ℝ) : ℝ :=
  E.cumulativeEval w (reindexFeature (finiteJetEquiv ι) φ)
    (fun i => v (finiteJetEquiv ι i)) (fun j i => q j (finiteJetEquiv ι i))
    ((coordinateEquiv (finiteJetEquiv ι)).symm x)

 

 theorem ClockTree.iteratedDeriv_finiteDisorderExpect {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (T : ClockTree S as)
    {a : ℝ} (ho : MassOrdered a as) (v : ι → ℝ) (q d : ℕ → ι → ℝ) {l r : ℝ}
    (hp : ∀ s ∈ Ioo l r, ∀ i, Monotone (fun j => q j i+s*d j i))
    (hr : ∀ s ∈ Ioo l r, ∀ i, v i ≤ q 0 i+s*d 0 i)
    (P : T.Assignment → ℝ) (x : ι → ℝ) (k : ℕ) {t : ℝ} (ht : t ∈ Ioo l r) :
    iteratedDeriv k (fun s => T.disorderExpect w φ v (fun j i => q j i+s*d j i) P x) t =
      ((T.testExpr P).finiteCumulativeCov φ d k).finiteCumulativeEval w φ v
        (fun j i => q j i+t*d j i) x := by
  let e := finiteJetEquiv ι
  have hd := T.iteratedDeriv_disorderExpect hw (reindexFeature e φ) ho
    (fun i => v (e i)) (fun j i => q j (e i)) (fun j i => d j (e i))
    (fun s hs i => hp s hs (e i)) (fun s hs i => hr s hs (e i)) P
    ((coordinateEquiv e).symm x) k ht
  have he (s : ℝ) : T.disorderExpect w (reindexFeature e φ) (fun i => v (e i))
      (fun j i => q j (e i)+s*d j (e i)) P ((coordinateEquiv e).symm x) =
      T.disorderExpect w φ v (fun j i => q j i+s*d j i) P x := by
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using
      T.disorderExpect_reindex e w φ v (fun j i => q j i+s*d j i) P ((coordinateEquiv e).symm x)
  simp only [he] at hd
  exact hd

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators
variable {S ι : Type*} [Fintype S] [Fintype ι] [Nonempty S] [Nonempty ι]
namespace ClockPolynomial
variable {as : List PositiveMass}

 
def finiteEval (P : ClockPolynomial S as) (w : S → ℝ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (t : ℝ) (v : ι → ℝ)
    (q : ℕ → ι → ℝ) (x : ι → ℝ) : ℝ :=
  P.rootEval w (reindexFeature (finiteJetEquiv ι) φ) t
    (fun i => q 0 (finiteJetEquiv ι i)-v (finiteJetEquiv ι i))
    (fun j i => q (j+1) (finiteJetEquiv ι i)-q j (finiteJetEquiv ι i))
    ((coordinateEquiv (finiteJetEquiv ι)).symm x)

 
def finiteLowJet (E : ClockExpr S as) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (b d : ℕ → ι → ℝ) (k : ℕ) : ClockPolynomial S as :=
  lowJet E (reindexFeature (finiteJetEquiv ι) φ)
    (fun i => b 0 (finiteJetEquiv ι i)) (fun i => d 0 (finiteJetEquiv ι i))
    (fun j i => b (j+1) (finiteJetEquiv ι i)-b j (finiteJetEquiv ι i))
    (fun j i => d (j+1) (finiteJetEquiv ι i)-d j (finiteJetEquiv ι i)) k

 

def finiteMixedJet (E : ClockExpr S as) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (b c d : ℕ → ι → ℝ) (l : ℝ) (k : ℕ) : ClockPolynomial S as :=
  (finiteLowJet E φ b d k).coeffDeriv ++
    (finiteLowJet E φ b d k).insert (reindexFeature (finiteJetEquiv ι) φ)
      (fun i => c 0 (finiteJetEquiv ι i)+l*d 0 (finiteJetEquiv ι i))
      (fun j i => (c (j+1) (finiteJetEquiv ι i)-c j (finiteJetEquiv ι i))+
        l*(d (j+1) (finiteJetEquiv ι i)-d j (finiteJetEquiv ι i)))

end ClockPolynomial

 

theorem ClockTree.mixed_finiteDisorderExpect {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (T : ClockTree S as)
    {a : ℝ} (ho : MassOrdered a as) (v : ι → ℝ) (q b c d : ℕ → ι → ℝ)
    {l₀ l₁ t₀ t₁ l t : ℝ}
    (hp : ∀ u ∈ Ioo l₀ l₁, ∀ s ∈ Ioo t₀ t₁, ∀ i,
      Monotone (fun j => q j i+s*c j i+u*(b j i+s*d j i)))
    (hr : ∀ u ∈ Ioo l₀ l₁, ∀ s ∈ Ioo t₀ t₁, ∀ i,
      v i ≤ q 0 i+s*c 0 i+u*(b 0 i+s*d 0 i))
    (hl : l ∈ Ioo l₀ l₁) (ht : t ∈ Ioo t₀ t₁)
    (P : T.Assignment → ℝ) (x : ι → ℝ) (k : ℕ) :
    HasDerivAt (fun s => iteratedDeriv k (fun u => T.disorderExpect w φ v
      (fun j i => q j i+s*c j i+u*(b j i+s*d j i)) P x) l)
      ((ClockPolynomial.finiteMixedJet (T.testExpr P) φ b c d l k).finiteEval w φ t v
        (fun j i => q j i+t*c j i+l*(b j i+t*d j i)) x) t := by
  let e := finiteJetEquiv ι
  let Δ (f : ℕ → ι → ℝ) := fun j i => f (j+1) (e i)-f j (e i)
  have hinc : ∀ j, ∀ u ∈ Ioo l₀ l₁, ∀ s ∈ Ioo t₀ t₁, ∀ i,
      0 ≤ Δ q j i+s*Δ c j i+u*(Δ b j i+s*Δ d j i) := by
    intro j u hu s hs i
    have hm := hp u hu s hs (e i) (Nat.le_succ j)
    dsimp [Δ]
    nlinarith
  have hroot : ∀ u ∈ Ioo l₀ l₁, ∀ s ∈ Ioo t₀ t₁, ∀ i,
      0 ≤ (q 0 (e i)-v (e i))+s*c 0 (e i)+u*(b 0 (e i)+s*d 0 (e i)) := by
    intro u hu s hs i
    linarith [hr u hu s hs (e i)]
  have hd := ClockPolynomial.mixed_lowJet_hasDerivAt hw (reindexFeature e φ)
    (T.testExpr P) ho (fun i => q 0 (e i)-v (e i))
    (fun i => b 0 (e i)) (fun i => c 0 (e i)) (fun i => d 0 (e i))
    (Δ q) (Δ b) (Δ c) (Δ d) hinc hroot hl ht ((coordinateEquiv e).symm x) k
  have he (u s : ℝ) : T.disorderExpect w φ v
      (fun j i => q j i+s*c j i+u*(b j i+s*d j i)) P x =
      (T.testExpr P).rootEval w (reindexFeature e φ)
        (fun i => (q 0 (e i)-v (e i))+s*c 0 (e i)+u*(b 0 (e i)+s*d 0 (e i)))
        (fun j i => Δ q j i+s*Δ c j i+u*(Δ b j i+s*Δ d j i))
        ((coordinateEquiv e).symm x) := by
    have hre := T.disorderExpect_reindex e w φ v
      (fun j i => q j i+s*c j i+u*(b j i+s*d j i)) P ((coordinateEquiv e).symm x)
    simp only [ContinuousLinearEquiv.apply_symm_apply] at hre
    rw [← hre,← T.rootEval_testExpr hw (reindexFeature e φ) ho]
    congr 1 <;> funext i
    · ring
    · funext z; dsimp [Δ]; ring
  simp only [he]
  convert hd using 1
  dsimp only [ClockPolynomial.finiteMixedJet,ClockPolynomial.finiteEval,
    ClockPolynomial.finiteLowJet,Δ,e] at ⊢
  congr 1 <;> funext i
  · ring
  · funext z; ring

end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set GaussianCalculus
open scoped Topology NNReal BigOperators
variable {S ι : Type*} [Fintype S] [Fintype ι] [Nonempty S] [Nonempty ι]
namespace ClockPolynomial
variable {as : List PositiveMass}

def finiteInsert (P : ClockPolynomial S as) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (d : ℕ → ι → ℝ) : ClockPolynomial S as :=
  P.insert (reindexFeature (finiteJetEquiv ι) φ)
    (fun i => d 0 (finiteJetEquiv ι i))
    (fun j i => d (j+1) (finiteJetEquiv ι i)-d j (finiteJetEquiv ι i))

 

theorem finiteEval_continuous {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (P : ClockPolynomial S as)
    (z : ℝ → ℝ) (hz : Continuous z) (v : ι → ℝ)
    (q : ℕ → ℝ → ι → ℝ) (hq : ∀ j, Continuous (q j))
    (x : ℝ → ι → ℝ) (hx : Continuous x) :
    Continuous (fun s => P.finiteEval w φ (z s) v (fun j => q j s) (x s)) := by
  induction P with
  | nil => exact continuous_const
  | cons p P ih =>
    have he := p.2.rootEval_continuous hw (reindexFeature (finiteJetEquiv ι) φ)
      (fun s i => q 0 s (finiteJetEquiv ι i)-v (finiteJetEquiv ι i))
      (fun j s i => q (j+1) s (finiteJetEquiv ι i)-q j s (finiteJetEquiv ι i))
      (by fun_prop) (by intro j; fun_prop)
      (fun s => (coordinateEquiv (finiteJetEquiv ι)).symm (x s)) (by fun_prop)
    exact ((p.1.continuous.comp hz).mul he).add ih

omit [Nonempty S] in
 theorem finiteEval_affine (P : ClockPolynomial S as) (w : S → ℝ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (z s : ℝ) (v : ι → ℝ) (q d : ℕ → ι → ℝ)
    (x : ι → ℝ) :
    P.finiteEval w φ z v (fun j i => q j i+s*d j i) x =
      P.rootEval w (reindexFeature (finiteJetEquiv ι) φ) z
        (fun i => (q 0 (finiteJetEquiv ι i)-v (finiteJetEquiv ι i))+s*d 0 (finiteJetEquiv ι i))
        (fun j i => (q (j+1) (finiteJetEquiv ι i)-q j (finiteJetEquiv ι i))+
          s*(d (j+1) (finiteJetEquiv ι i)-d j (finiteJetEquiv ι i)))
        ((coordinateEquiv (finiteJetEquiv ι)).symm x) := by
  unfold finiteEval
  congr 1 <;> funext i
  · ring
  · funext j; ring

 theorem hasDerivAt_finite_frozen {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (P : ClockPolynomial S as)
    {a : ℝ} (ho : MassOrdered a as) (v : ι → ℝ) (q d : ℕ → ι → ℝ) {l r t : ℝ}
    (hp : ∀ s ∈ Ioo l r, ∀ i, Monotone (fun j => q j i+s*d j i))
    (hr : ∀ s ∈ Ioo l r, ∀ i, v i ≤ q 0 i+s*d 0 i) (ht : t ∈ Ioo l r)
    (z : ℝ) (x : ι → ℝ) :
    HasDerivAt (fun s => P.finiteEval w φ z v (fun j i => q j i+s*d j i) x)
      ((P.finiteInsert φ d).finiteEval w φ z v (fun j i => q j i+t*d j i) x) t := by
  simp only [finiteEval_affine]
  apply P.hasDerivAt_frozen hw (reindexFeature (finiteJetEquiv ι) φ) ho
  · intro j s hs i
    nlinarith [hp s hs (finiteJetEquiv ι i) (Nat.le_succ j)]
  · intro s hs i
    linarith [hr s hs (finiteJetEquiv ι i)]
  · exact ht

 theorem hasDerivAt_finite_diagonal {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (P : ClockPolynomial S as)
    {a : ℝ} (ho : MassOrdered a as) (v : ι → ℝ) (q d : ℕ → ι → ℝ) {l r t : ℝ}
    (hp : ∀ s ∈ Ioo l r, ∀ i, Monotone (fun j => q j i+s*d j i))
    (hr : ∀ s ∈ Ioo l r, ∀ i, v i ≤ q 0 i+s*d 0 i) (ht : t ∈ Ioo l r)
    (x : ι → ℝ) :
    HasDerivAt (fun s => P.finiteEval w φ s v (fun j i => q j i+s*d j i) x)
      ((P.coeffDeriv++P.finiteInsert φ d).finiteEval w φ t v
        (fun j i => q j i+t*d j i) x) t := by
  simp only [finiteEval_affine]
  apply P.hasDerivAt_diagonal hw (reindexFeature (finiteJetEquiv ι) φ) ho
  · intro j s hs i
    nlinarith [hp s hs (finiteJetEquiv ι i) (Nat.le_succ j)]
  · intro s hs i
    linarith [hr s hs (finiteJetEquiv ι i)]
  · exact ht

 theorem finiteLowJet_succ_eval {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (E : ClockExpr S as) {a : ℝ} (ho : MassOrdered a as)
    (b d : ℕ → ι → ℝ) (k : ℕ) (t : ℝ) (v : ι → ℝ) (q : ℕ → ι → ℝ) (x : ι → ℝ) :
    (finiteLowJet E φ b d (k+1)).finiteEval w φ t v q x =
      ((finiteLowJet E φ b d k).finiteInsert φ (fun j i => b j i+t*d j i)).finiteEval
        w φ t v q x := by
  unfold finiteLowJet finiteEval finiteInsert
  rw [lowJet]
  rw [rootEval_affineInsert hw _ _ ho]
  congr 2
  funext j i
  ring

 theorem finiteLowJet_hasDerivAt_low {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (E : ClockExpr S as) {a : ℝ} (ho : MassOrdered a as)
    (v : ι → ℝ) (q b d : ℕ → ι → ℝ) (k : ℕ) (t : ℝ) {l r u : ℝ}
    (hp : ∀ s ∈ Ioo l r, ∀ i, Monotone (fun j => q j i+s*(b j i+t*d j i)))
    (hr : ∀ s ∈ Ioo l r, ∀ i, v i ≤ q 0 i+s*(b 0 i+t*d 0 i))
    (hu : u ∈ Ioo l r) (x : ι → ℝ) :
    HasDerivAt (fun s => (finiteLowJet E φ b d k).finiteEval w φ t v
      (fun j i => q j i+s*(b j i+t*d j i)) x)
      ((finiteLowJet E φ b d (k+1)).finiteEval w φ t v
        (fun j i => q j i+u*(b j i+t*d j i)) x) u := by
  rw [finiteLowJet_succ_eval hw φ E ho]
  exact hasDerivAt_finite_frozen hw φ _ ho v q _ hp hr hu t x

 

 theorem finiteLowJet_hasDerivAt_high {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (E : ClockExpr S as) {a : ℝ} (ho : MassOrdered a as)
    (v : ι → ℝ) (q b c d : ℕ → ι → ℝ) (k : ℕ) (l : ℝ) {t₀ t₁ t : ℝ}
    (hp : ∀ s ∈ Ioo t₀ t₁, ∀ i, Monotone (fun j => q j i+s*c j i+l*(b j i+s*d j i)))
    (hr : ∀ s ∈ Ioo t₀ t₁, ∀ i, v i ≤ q 0 i+s*c 0 i+l*(b 0 i+s*d 0 i))
    (ht : t ∈ Ioo t₀ t₁) (x : ι → ℝ) :
    HasDerivAt (fun s => (finiteLowJet E φ b d k).finiteEval w φ s v
      (fun j i => q j i+s*c j i+l*(b j i+s*d j i)) x)
      ((finiteMixedJet E φ b c d l k).finiteEval w φ t v
        (fun j i => q j i+t*c j i+l*(b j i+t*d j i)) x) t := by
  have he (s : ℝ) : (fun j i => (q j i+l*b j i)+s*(c j i+l*d j i)) =
      (fun j i => q j i+s*c j i+l*(b j i+s*d j i)) := by funext j i; ring
  have hpn : ∀ s ∈ Ioo t₀ t₁, ∀ i,
      Monotone (fun j => (q j i+l*b j i)+s*(c j i+l*d j i)) := by
    intro s hs i j j' hj
    have H := hp s hs i hj
    nlinarith
  have hrn : ∀ s ∈ Ioo t₀ t₁, ∀ i,
      v i ≤ (q 0 i+l*b 0 i)+s*(c 0 i+l*d 0 i) := by
    intro s hs i
    nlinarith [hr s hs i]
  have hd := hasDerivAt_finite_diagonal hw φ (finiteLowJet E φ b d k) ho v
    (fun j i => q j i+l*b j i) (fun j i => c j i+l*d j i) hpn hrn ht x
  simp only [he] at hd
  convert hd using 1
  unfold finiteMixedJet finiteInsert
  congr 3
  funext j i
  ring

end ClockPolynomial
end SKFluctuations.Hierarchy

 

namespace SKFluctuations.Cavity
open MeasureTheory ProbabilityTheory Filter Set Hierarchy GaussianCalculus
open scoped Topology NNReal BigOperators

 

def cutFullVariance (n : ℕ) (q : ℕ → RestCoordinate n → ℝ) (U : ℕ) (l t : ℝ)
    (b h K : ℕ → ℝ) (j : ℕ) : FullCoordinate n → ℝ :=
  fullVariance n (q j) t (relocatedClock U l b j) (relocatedClock U l h j)
    (relocatedClock U l K j)

def rowInterpolationSlope (n : ℕ) (b h K : ℝ) : FullCoordinate n → ℝ :=
  Sum.elim (Sum.elim (fun _ => 0) (fun _ => -K))
    (Sum.elim (fun _ => b) (fun _ => h))

def cutTBase (n : ℕ) (q : ℕ → RestCoordinate n → ℝ) (U : ℕ) (l : ℝ)
    (b h K : ℕ → ℝ) := cutFullVariance n q U l 0 b h K

def cutTSlope (n : ℕ) (U : ℕ) (l : ℝ) (b h K : ℕ → ℝ) (j : ℕ) :=
  rowInterpolationSlope n (relocatedClock U l b j) (relocatedClock U l h j)
    (relocatedClock U l K j)

theorem cutFullVariance_t_affine (n : ℕ) (q : ℕ → RestCoordinate n → ℝ)
    (U : ℕ) (l t : ℝ) (b h K : ℕ → ℝ) :
    cutFullVariance n q U l t b h K =
      fun j i => cutTBase n q U l b h K j i+t*cutTSlope n U l b h K j i := by
  funext j i
  rcases i with (i | i) | (i | i) <;>
    simp only [cutFullVariance,cutTBase,cutTSlope,fullVariance,rowInterpolationSlope,
      Sum.elim_inl,Sum.elim_inr] <;> ring

theorem cutFullVariance_nonneg (n : ℕ) (q : ℕ → RestCoordinate n → ℝ)
    (U : ℕ) {l t : ℝ} (hl : l ∈ Icc (0:ℝ) 1) (ht : t ∈ Icc (0:ℝ) 1)
    {b h K : ℕ → ℝ} (hq : ∀ j i, 0 ≤ q j i) (hb : ∀ j, 0 ≤ b j)
    (hh : ∀ j, 0 ≤ h j) (hK : ∀ j, 0 ≤ K j) (j : ℕ) (i : FullCoordinate n) :
    0 ≤ cutFullVariance n q U l t b h K j i :=
  fullVariance_nonneg n (q j) (hq j) ht
    (relocatedClock_nonneg U hl.1 hb j) (relocatedClock_nonneg U hl.1 hh j)
    (relocatedClock_nonneg U hl.1 hK j) i

theorem cutFullVariance_monotone (n : ℕ) (q : ℕ → RestCoordinate n → ℝ)
    (U : ℕ) {l t : ℝ} (hl : l ∈ Icc (0:ℝ) 1) (ht : t ∈ Icc (0:ℝ) 1)
    {b h K : ℕ → ℝ} (hq : ∀ i, Monotone (fun j => q j i))
    (hb : ∀ j, 0 ≤ b j) (hh : ∀ j, 0 ≤ h j) (hK : ∀ j, 0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K) (i : FullCoordinate n) :
    Monotone (fun j => cutFullVariance n q U l t b h K j i) :=
  fullVariance_monotone n ht hq (relocatedClock_monotone U hl hbm hb)
    (relocatedClock_monotone U hl hhm hh) (relocatedClock_monotone U hl hKm hK) i

theorem cutT_affine_monotone (n : ℕ) (q : ℕ → RestCoordinate n → ℝ)
    (U : ℕ) {l : ℝ} (hl : l ∈ Icc (0:ℝ) 1)
    {b h K : ℕ → ℝ} (hq : ∀ i, Monotone (fun j => q j i))
    (hb : ∀ j, 0 ≤ b j) (hh : ∀ j, 0 ≤ h j) (hK : ∀ j, 0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K) :
    ∀ t ∈ Ioo (0:ℝ) 1, ∀ i, Monotone (fun j =>
      cutTBase n q U l b h K j i+t*cutTSlope n U l b h K j i) := by
  intro t ht i
  have hm := cutFullVariance_monotone n q U hl ⟨ht.1.le,ht.2.le⟩ hq hb hh hK hbm hhm hKm i
  simpa only [cutFullVariance_t_affine] using hm

 

theorem hasDerivAt_cutDisorderExpect_t (n : ℕ) (q : ℕ → RestCoordinate n → ℝ)
    (U : ℕ) {l t : ℝ} (hl : l ∈ Icc (0:ℝ) 1) (ht : t ∈ Ioo (0:ℝ) 1)
    (b h K : ℕ → ℝ) (hq0 : ∀ j i, 0 ≤ q j i) (hq : ∀ i, Monotone (fun j => q j i))
    (hb : ∀ j, 0 ≤ b j) (hh : ∀ j, 0 ≤ h j) (hK : ∀ j, 0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K)
    {as : List PositiveMass} (T : ClockTree (Spin n × Bool) as)
    (P : T.Assignment → ℝ) (x : FullCoordinate n → ℝ) :
    HasDerivAt (fun s => T.disorderExpect (fullWeight n) (fullFeature n) 0
      (cutFullVariance n q U l s b h K) P x)
      (∑ σ, T.finiteDisorderRate (fullWeight_pos n) (fullFeature n) 0
        (cutTBase n q U l b h K) (cutTSlope n U l b h K)
        (cutT_affine_monotone n q U hl hq hb hh hK hbm hhm hKm) σ t x*P σ) t := by
  have hr : ∀ s ∈ Ioo (0:ℝ) 1, ∀ i, (0 : FullCoordinate n → ℝ) i ≤
      cutTBase n q U l b h K 0 i+s*cutTSlope n U l b h K 0 i := by
    intro s hs i
    have hn := cutFullVariance_nonneg n q U hl ⟨hs.1.le,hs.2.le⟩ hq0 hb hh hK 0 i
    simpa only [cutFullVariance_t_affine, Pi.zero_apply] using hn
  have hd := T.hasDerivAt_finiteDisorderExpect (fullWeight_pos n) (fullFeature n) 0
    (cutTBase n q U l b h K) (cutTSlope n U l b h K)
    (cutT_affine_monotone n q U hl hq hb hh hK hbm hhm hKm) hr P ht x
  simpa only [cutFullVariance_t_affine] using hd

 

def cutLBase (n : ℕ) (q : ℕ → RestCoordinate n → ℝ) (U : ℕ) (t : ℝ)
    (b h K : ℕ → ℝ) := cutFullVariance n q U 0 t b h K

def cutLSlope (n : ℕ) (U : ℕ) (t : ℝ) (b h K : ℕ → ℝ) (j : ℕ) : FullCoordinate n → ℝ :=
  if j < U then fullVariance n 0 t (b j) (h j) (K j) else 0

theorem cutFullVariance_l_affine (n : ℕ) (q : ℕ → RestCoordinate n → ℝ)
    (U : ℕ) (l t : ℝ) (b h K : ℕ → ℝ) :
    cutFullVariance n q U l t b h K =
      fun j i => cutLBase n q U t b h K j i+l*cutLSlope n U t b h K j i := by
  funext j i
  rcases i with (i | i) | (i | i) <;>
    simp only [cutFullVariance,cutLBase,cutLSlope,fullVariance,relocatedClock,
      Sum.elim_inl,Sum.elim_inr] <;> split_ifs <;> simp_all <;> ring

theorem cutL_affine_monotone (n : ℕ) (q : ℕ → RestCoordinate n → ℝ)
    (U : ℕ) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1)
    {b h K : ℕ → ℝ} (hq : ∀ i, Monotone (fun j => q j i))
    (hb : ∀ j, 0 ≤ b j) (hh : ∀ j, 0 ≤ h j) (hK : ∀ j, 0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K) :
    ∀ l ∈ Ioo (0:ℝ) 1, ∀ i, Monotone (fun j =>
      cutLBase n q U t b h K j i+l*cutLSlope n U t b h K j i) := by
  intro l hl i
  have hm := cutFullVariance_monotone n q U ⟨hl.1.le,hl.2.le⟩ ht hq hb hh hK hbm hhm hKm i
  simpa only [cutFullVariance_l_affine] using hm

 

theorem hasDerivAt_cutDisorderExpect_l (n : ℕ) (q : ℕ → RestCoordinate n → ℝ)
    (U : ℕ) {l t : ℝ} (hl : l ∈ Ioo (0:ℝ) 1) (ht : t ∈ Icc (0:ℝ) 1)
    (b h K : ℕ → ℝ) (hq0 : ∀ j i, 0 ≤ q j i) (hq : ∀ i, Monotone (fun j => q j i))
    (hb : ∀ j, 0 ≤ b j) (hh : ∀ j, 0 ≤ h j) (hK : ∀ j, 0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K)
    {as : List PositiveMass} (T : ClockTree (Spin n × Bool) as)
    (P : T.Assignment → ℝ) (x : FullCoordinate n → ℝ) :
    HasDerivAt (fun s => T.disorderExpect (fullWeight n) (fullFeature n) 0
      (cutFullVariance n q U s t b h K) P x)
      (∑ σ, T.finiteDisorderRate (fullWeight_pos n) (fullFeature n) 0
        (cutLBase n q U t b h K) (cutLSlope n U t b h K)
        (cutL_affine_monotone n q U ht hq hb hh hK hbm hhm hKm) σ l x*P σ) l := by
  have hr : ∀ s ∈ Ioo (0:ℝ) 1, ∀ i, (0 : FullCoordinate n → ℝ) i ≤
      cutLBase n q U t b h K 0 i+s*cutLSlope n U t b h K 0 i := by
    intro s hs i
    have hn := cutFullVariance_nonneg n q U ⟨hs.1.le,hs.2.le⟩ ht hq0 hb hh hK 0 i
    simpa only [cutFullVariance_l_affine, Pi.zero_apply] using hn
  have hd := T.hasDerivAt_finiteDisorderExpect (fullWeight_pos n) (fullFeature n) 0
    (cutLBase n q U t b h K) (cutLSlope n U t b h K)
    (cutL_affine_monotone n q U ht hq hb hh hK hbm hhm hKm) hr P hl x
  simpa only [cutFullVariance_l_affine] using hd

end SKFluctuations.Cavity

 

namespace SKFluctuations.Cavity
open MeasureTheory ProbabilityTheory Filter Set Hierarchy GaussianCalculus
open scoped Topology NNReal BigOperators

 

 theorem iteratedDeriv_cutDisorderExpect_l (n : ℕ) (q : ℕ → RestCoordinate n → ℝ)
    (U : ℕ) {l t : ℝ} (hl : l ∈ Ioo (0:ℝ) 1) (ht : t ∈ Icc (0:ℝ) 1)
    (b h K : ℕ → ℝ) (hq0 : ∀ j i, 0 ≤ q j i) (hq : ∀ i, Monotone (fun j => q j i))
    (hb : ∀ j, 0 ≤ b j) (hh : ∀ j, 0 ≤ h j) (hK : ∀ j, 0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K)
    {as : List PositiveMass} (T : ClockTree (Spin n × Bool) as) (ho : MassOrdered 0 as)
    (P : T.Assignment → ℝ) (x : FullCoordinate n → ℝ) (k : ℕ) :
    iteratedDeriv k (fun s => T.disorderExpect (fullWeight n) (fullFeature n) 0
      (cutFullVariance n q U s t b h K) P x) l =
      ((T.testExpr P).finiteCumulativeCov (fullFeature n) (cutLSlope n U t b h K) k).finiteCumulativeEval (fullWeight n) (fullFeature n) 0
          (cutFullVariance n q U l t b h K) x := by
  have hr : ∀ s ∈ Ioo (0:ℝ) 1, ∀ i, (0 : FullCoordinate n → ℝ) i ≤
      cutLBase n q U t b h K 0 i+s*cutLSlope n U t b h K 0 i := by
    intro s hs i
    have hn := cutFullVariance_nonneg n q U ⟨hs.1.le,hs.2.le⟩ ht hq0 hb hh hK 0 i
    simpa only [cutFullVariance_l_affine,Pi.zero_apply] using hn
  simpa only [cutFullVariance_l_affine] using
    T.iteratedDeriv_finiteDisorderExpect (fullWeight_pos n) (fullFeature n) ho 0
      (cutLBase n q U t b h K) (cutLSlope n U t b h K)
      (cutL_affine_monotone n q U ht hq hb hh hK hbm hhm hKm) hr P x k hl

 

 theorem iteratedDeriv_cutDisorderExpect_t (n : ℕ) (q : ℕ → RestCoordinate n → ℝ)
    (U : ℕ) {l t : ℝ} (hl : l ∈ Icc (0:ℝ) 1) (ht : t ∈ Ioo (0:ℝ) 1)
    (b h K : ℕ → ℝ) (hq0 : ∀ j i, 0 ≤ q j i) (hq : ∀ i, Monotone (fun j => q j i))
    (hb : ∀ j, 0 ≤ b j) (hh : ∀ j, 0 ≤ h j) (hK : ∀ j, 0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K)
    {as : List PositiveMass} (T : ClockTree (Spin n × Bool) as) (ho : MassOrdered 0 as)
    (P : T.Assignment → ℝ) (x : FullCoordinate n → ℝ) (k : ℕ) :
    iteratedDeriv k (fun s => T.disorderExpect (fullWeight n) (fullFeature n) 0
      (cutFullVariance n q U l s b h K) P x) t =
      ((T.testExpr P).finiteCumulativeCov (fullFeature n) (cutTSlope n U l b h K) k).finiteCumulativeEval (fullWeight n) (fullFeature n) 0
          (cutFullVariance n q U l t b h K) x := by
  have hr : ∀ s ∈ Ioo (0:ℝ) 1, ∀ i, (0 : FullCoordinate n → ℝ) i ≤
      cutTBase n q U l b h K 0 i+s*cutTSlope n U l b h K 0 i := by
    intro s hs i
    have hn := cutFullVariance_nonneg n q U hl ⟨hs.1.le,hs.2.le⟩ hq0 hb hh hK 0 i
    simpa only [cutFullVariance_t_affine,Pi.zero_apply] using hn
  simpa only [cutFullVariance_t_affine] using
    T.iteratedDeriv_finiteDisorderExpect (fullWeight_pos n) (fullFeature n) ho 0
      (cutTBase n q U l b h K) (cutTSlope n U l b h K)
      (cutT_affine_monotone n q U hl hq hb hh hK hbm hhm hKm) hr P x k ht

end SKFluctuations.Cavity

end

end OAI
