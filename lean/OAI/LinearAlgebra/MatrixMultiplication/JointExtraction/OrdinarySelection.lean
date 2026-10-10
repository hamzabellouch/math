import OAI.LinearAlgebra.MatrixMultiplication.JointExtraction.CoarseHashing
import OAI.LinearAlgebra.MatrixMultiplication.JointExtraction.ExtractionRates

namespace OAI

/-! Joint tensor extraction, compatibility and entropy estimates. -/

noncomputable section

namespace MatrixMultiplication.JointOrdinarySelection

open JointCoarseHashing JointExtractionRates Filter
open scoped BigOperators Topology

attribute [local instance] Classical.propDecidable

variable {P E : Type*}

def neighbors (ambient : Finset (Triple P)) (e : Triple P) : Finset (Triple P) :=
  ambient.filter (fun f => f ≠ e ∧ SharesSide e f)

@[simp] theorem mem_neighbors (ambient : Finset (Triple P)) (e f : Triple P) :
    f ∈ neighbors ambient e ↔ f ∈ ambient ∧ f ≠ e ∧ SharesSide e f := by
  simp only [neighbors, Finset.mem_filter]

section Finite

variable [Fintype P]

def Bad (k : ℕ) (U : Finset (ZMod (37 ^ k))) (ambient : Finset (Triple P))
    (e : Triple P) (s : Sample P k) : Prop :=
  ∃ f ∈ neighbors ambient e, Survives k U f s

def Good (k : ℕ) (U : Finset (ZMod (37 ^ k))) (ambient : Finset (Triple P))
    (e : Triple P) (s : Sample P k) : Prop :=
  Survives k U e s ∧ ¬ Bad k U ambient e s

def goodEvent (k : ℕ) (U : Finset (ZMod (37 ^ k))) (ambient : Finset (Triple P))
    (e : Triple P) : Finset (Sample P k) :=
  (ownEvent k U e).filter (fun s => ¬ Bad k U ambient e s)

@[simp] theorem mem_goodEvent (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (ambient : Finset (Triple P)) (e : Triple P) (s : Sample P k) :
    s ∈ goodEvent k U ambient e ↔ Good k U ambient e s := by
  simp only [goodEvent, ownEvent, Finset.mem_filter, Finset.mem_univ, true_and, Good]

theorem good_excludes_neighbor (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (ambient : Finset (Triple P)) (e f : Triple P) (s : Sample P k)
    (hg : Good k U ambient e s) (hf : f ∈ ambient) (hne : f ≠ e)
    (hshare : SharesSide e f) : ¬ Survives k U f s := by
  intro hs
  exact hg.2 ⟨f, (mem_neighbors ambient e f).2 ⟨hf, hne, hshare⟩, hs⟩

theorem good_no_shared_side (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (ambient : Finset (Triple P)) (e f : Triple P) (s : Sample P k)
    (he : Good k U ambient e s) (hf : Good k U ambient f s)
    (hmem : f ∈ ambient) (hne : f ≠ e) : ¬ SharesSide e f := by
  intro hshare
  exact good_excludes_neighbor k U ambient e f s he hmem hne hshare hf.1

theorem ownEvent_card_real (k : ℕ) (U : Finset (ZMod (37 ^ k))) (e : Triple P) :
    ((ownEvent k U e).card : ℝ) =
      ((U.card : ℝ) / ((37 ^ k : ℕ) : ℝ) ^ 2) * (Fintype.card (Sample P k) : ℝ) := by
  have hsample : (Fintype.card (Sample P k) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hf : ((ownEvent k U e).card : ℝ) / (Fintype.card (Sample P k) : ℝ) =
      (U.card : ℝ) / ((37 ^ k : ℕ) : ℝ) ^ 2 := by
    change
      ((Finset.univ.filter (fun s =>
        JointHashing.Survives (U : Set (ZMod (37 ^ k)))
          (castWord k e.1) (castWord k e.2.1) s)).card : ℝ) /
        (Fintype.card (JointHashing.Sample P (ZMod (37 ^ k))) : ℝ) = _
    simpa only [Fintype.card_subtype, ZMod.card] using
      JointHashing.survival_fraction U (castWord k e.1) (castWord k e.2.1)
  exact (div_eq_iff hsample).mp hf

theorem bad_card_le (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (ambient : Finset (Triple P)) (S : P → ℕ)
    (hsupport : ∀ f ∈ ambient, HasSupportSum S f)
    (e : Triple P) (he : e ∈ ambient) :
    (((ownEvent k U e).filter (Bad k U ambient e)).card : ℝ) ≤
      ((neighbors ambient e).card : ℝ) / ((37 ^ k : ℕ) : ℝ) *
        ((ownEvent k U e).card : ℝ) := by
  have hset : (ownEvent k U e).filter (Bad k U ambient e) =
      (ownEvent k U e).filter (fun s => ∃ f ∈ neighbors ambient e, Survives k U f s) := by
    ext s
    simp only [Finset.mem_filter, Bad]
  rw [hset]
  apply competitor_union_card_le k U S e (hsupport e he) (neighbors ambient e)
  · intro f hf
    exact hsupport f ((mem_neighbors ambient e f).mp hf).1
  · intro f hf
    exact ((mem_neighbors ambient e f).mp hf).2.1
  · intro f hf
    exact ((mem_neighbors ambient e f).mp hf).2.2

theorem goodEvent_card_lower (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (ambient : Finset (Triple P)) (S : P → ℕ)
    (hsupport : ∀ f ∈ ambient, HasSupportSum S f)
    (e : Triple P) (he : e ∈ ambient) (D : ℕ)
    (hdegree : (neighbors ambient e).card ≤ D)
    (hsmall : (D : ℝ) / ((37 ^ k : ℕ) : ℝ) ≤ 1 / 2) :
    ((U.card : ℝ) / ((37 ^ k : ℕ) : ℝ) ^ 2 / 2) *
      (Fintype.card (Sample P k) : ℝ) ≤ (goodEvent k U ambient e).card := by
  have hM : (0 : ℝ) ≤ ((37 ^ k : ℕ) : ℝ) := Nat.cast_nonneg _
  have hdeg : ((neighbors ambient e).card : ℝ) / ((37 ^ k : ℕ) : ℝ) ≤ 1 / 2 :=
    (div_le_div_of_nonneg_right (by exact_mod_cast hdegree) hM).trans hsmall
  have hb : (((ownEvent k U e).filter (Bad k U ambient e)).card : ℝ) ≤
      (1 / 2) * ((ownEvent k U e).card : ℝ) :=
    (bad_card_le k U ambient S hsupport e he).trans
      (mul_le_mul_of_nonneg_right hdeg (Nat.cast_nonneg _))
  have hg := JointLossCounts.good_card_lower (ownEvent k U e) (Bad k U ambient e)
    (1 / 2) hb
  rw [ownEvent_card_real] at hg
  change _ ≤ ((goodEvent k U ambient e).card : ℝ) at hg
  convert hg using 1
  ring

theorem goodIncidence_eq (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (ambient : Finset (Triple P)) (coarse : E → Triple P) (e : E) :
    goodIncidence (fun s e => Good k U ambient (coarse e) s) e =
      (goodEvent k U ambient (coarse e)).card := by
  unfold goodIncidence
  congr 1
  ext s
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_goodEvent]

theorem exists_selection_of_degree_bound [Fintype E]
    (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (ambient : Finset (Triple P)) (S : P → ℕ) (coarse : E → Triple P)
    (hinj : Function.Injective coarse)
    (hsupport : ∀ f ∈ ambient, HasSupportSum S f)
    (htarget : ∀ e, coarse e ∈ ambient) (D : ℕ)
    (hdegree : ∀ e, (neighbors ambient (coarse e)).card ≤ D)
    (hsmall : (D : ℝ) / ((37 ^ k : ℕ) : ℝ) ≤ 1 / 2)
    (K : ℕ) (hK : (K : ℝ) ≤ (Fintype.card E : ℝ) *
      ((U.card : ℝ) / ((37 ^ k : ℕ) : ℝ) ^ 2 / 2)) :
    ∃ (s : Sample P k) (G : Finset E), G.card = K ∧
      (∀ e ∈ G, Good k U ambient (coarse e) s) ∧
      (G : Set E).Pairwise (fun e f => ¬ SharesSide (coarse e) (coarse f)) := by
  classical
  have hi (e : E) :
      ((U.card : ℝ) / ((37 ^ k : ℕ) : ℝ) ^ 2 / 2) *
        (Fintype.card (Sample P k) : ℝ) ≤
      (goodIncidence (fun s e => Good k U ambient (coarse e) s) e : ℝ) := by
    rw [goodIncidence_eq]
    exact goodEvent_card_lower k U ambient S hsupport (coarse e) (htarget e) D
      (hdegree e) hsmall
  obtain ⟨s, hs⟩ := exists_goodCount_ge (fun s e => Good k U ambient (coarse e) s) _ hi
  have hk : K ≤ goodCount (fun s e => Good k U ambient (coarse e) s) s := by
    exact_mod_cast hK.trans hs
  obtain ⟨G, hcard, hgood⟩ := exists_good_subfamily
    (fun s e => Good k U ambient (coarse e) s) s K hk
  refine ⟨s, G, hcard, hgood, ?_⟩
  intro e he f hf hne
  exact good_no_shared_side k U ambient (coarse e) (coarse f) s
    (hgood e he) (hgood f hf) (htarget f) (fun h => hne (hinj h).symm)

theorem exists_selection_floor [Fintype E]
    (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (ambient : Finset (Triple P)) (S : P → ℕ) (coarse : E → Triple P)
    (hinj : Function.Injective coarse)
    (hsupport : ∀ f ∈ ambient, HasSupportSum S f)
    (htarget : ∀ e, coarse e ∈ ambient) (D : ℕ)
    (hdegree : ∀ e, (neighbors ambient (coarse e)).card ≤ D)
    (hsmall : (D : ℝ) / ((37 ^ k : ℕ) : ℝ) ≤ 1 / 2) :
    ∃ (s : Sample P k) (G : Finset E),
      G.card = ⌊(Fintype.card E : ℝ) *
        ((U.card : ℝ) / ((37 ^ k : ℕ) : ℝ) ^ 2 / 2)⌋₊ ∧
      (∀ e ∈ G, Good k U ambient (coarse e) s) ∧
      (G : Set E).Pairwise (fun e f => ¬ SharesSide (coarse e) (coarse f)) := by
  apply exists_selection_of_degree_bound k U ambient S coarse hinj hsupport htarget D
    hdegree hsmall _ (Nat.floor_le ?_)
  positivity

end Finite

def hashLevel (H : ℝ) (N : ℕ) : ℕ := ⌊(N : ℝ) * H / Real.log 37⌋₊ + 1

def hashSet (H : ℝ) (N : ℕ) : Finset (ZMod (37 ^ hashLevel H N)) :=
  JointAPFree.modularSet (hashModulus H N)

theorem hashSet_AP (H : ℝ) (N : ℕ) :
    ∀ x ∈ hashSet H N, ∀ y ∈ hashSet H N, ∀ z ∈ hashSet H N,
      x + y = 2 * z → x = z ∧ y = z :=
  JointAPFree.modularSet_hashAP (hashModulus H N)

theorem eventually_exists_selection
    {P E : ℕ → Type*} [∀ N, Fintype (P N)] [∀ N, Fintype (E N)]
    (ambient : ∀ N, Finset (Triple (P N))) (S : ∀ N, P N → ℕ)
    (coarse : ∀ N, E N → Triple (P N))
    (hinj : ∀ N, Function.Injective (coarse N))
    (hsupport : ∀ N, ∀ f ∈ ambient N, HasSupportSum (S N) f)
    (htarget : ∀ N e, coarse N e ∈ ambient N)
    (degree : ℕ → ℕ)
    (hdegree : ∀ N e, (neighbors (ambient N) (coarse N e)).card ≤ degree N)
    {A D H : ℝ} (hH : 0 ≤ H) (hgap : D < H)
    (hdegreeRate : ∀ η : ℝ, 0 < η →
      ∀ᶠ N in atTop, Real.log (degree N : ℝ) / (N : ℝ) ≤ D + η)
    (hpos : ∀ᶠ N in atTop, 0 < Fintype.card (E N))
    (hE : Tendsto (fun N => Real.log (Fintype.card (E N) : ℝ) / (N : ℝ))
      atTop (𝓝 A))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∃ (s : Sample (P N) (hashLevel H N)) (G : Finset (E N)),
      G.card = ⌊Real.exp ((N : ℝ) * (A - H - ε))⌋₊ ∧
      (∀ e ∈ G, Good (hashLevel H N) (hashSet H N) (ambient N) (coarse N e) s) ∧
      (G : Set (E N)).Pairwise (fun e f => ¬ SharesSide (coarse N e) (coarse N f)) := by
  classical
  let c : ℝ := (H - D) / 2
  have hc : 0 < c := by dsimp [c]; linarith
  have hclt : c < H - D := by dsimp [c]; linarith
  have hratio := eventually_degree_div_hashModulus_le_exp hH hdegreeRate hclt
  have hsmall : ∀ᶠ N in atTop,
      (degree N : ℝ) / (hashModulus H N : ℝ) ≤ 1 / 2 := by
    apply eventually_error_le_half 1 0 hc
    simpa only [pow_zero, one_mul] using hratio
  let good := fun N (s : Sample (P N) (hashLevel H N)) (e : E N) =>
    Good (hashLevel H N) (hashSet H N) (ambient N) (coarse N e) s
  have hinc : ∀ᶠ N in atTop, ∀ e,
      (((JointAPFree.modularSet (hashModulus H N)).card : ℝ) /
        (hashModulus H N : ℝ) ^ 2 / 2) *
        (Fintype.card (Sample (P N) (hashLevel H N)) : ℝ) ≤
          (goodIncidence (good N) e : ℝ) := by
    filter_upwards [hsmall] with N hN e
    rw [show goodIncidence (good N) e =
        (goodEvent (hashLevel H N) (hashSet H N) (ambient N) (coarse N e)).card from
      goodIncidence_eq _ _ _ _ _]
    exact goodEvent_card_lower (hashLevel H N) (hashSet H N) (ambient N) (S N)
      (hsupport N) (coarse N e) (htarget N e) (degree N) (hdegree N e) hN
  have hyield := eventually_exists_many_good_explicit good hH hpos hinc hE hε
  have hselection := eventually_exists_good_subfamily good
    (fun N => ⌊Real.exp ((N : ℝ) * (A - H - ε))⌋₊) hyield
  filter_upwards [hselection] with N hN
  obtain ⟨s, G, hcard, hgood⟩ := hN
  refine ⟨s, G, hcard, hgood, ?_⟩
  intro e he f hf hne
  exact good_no_shared_side (hashLevel H N) (hashSet H N) (ambient N)
    (coarse N e) (coarse N f) s (hgood e he) (hgood f hf) (htarget N f)
    (fun h => hne ((hinj N) h).symm)

end MatrixMultiplication.JointOrdinarySelection

end

end OAI
