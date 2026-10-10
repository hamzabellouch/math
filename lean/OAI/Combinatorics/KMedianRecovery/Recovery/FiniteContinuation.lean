import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.MergeCross
import OAI.Combinatorics.KMedianRecovery.Geometry.NearestMap

namespace OAI

namespace MetricKMedianRecovery.FiniteLabelContinuation
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion CanonicalMergeCrossing
variable {X : Type*} [LinearOrder X] {d : ℕ}

def alphabet (loc : Fin d → X) (F Q : Finset X) : List X :=
  (F ∪ Q ∪ Finset.univ.image loc).sort (·≤·)

lemma mem_alphabet (loc : Fin d → X) (F Q : Finset X) (x : X) :
    x∈alphabet loc F Q ↔ x∈F ∨ x∈Q ∨ ∃ j,loc j=x := by
  simp only [alphabet,Finset.mem_sort,Finset.mem_union,Finset.mem_image,Finset.mem_univ,true_and]
  tauto

lemma alphabet_nodup (loc : Fin d → X) (F Q : Finset X) : (alphabet loc F Q).Nodup :=
  Finset.sort_nodup _ _

lemma alphabet_length (loc : Fin d → X) (F Q : Finset X) :
    (alphabet loc F Q).length ≤ F.card+Q.card+d := by
  rw [alphabet,Finset.length_sort]
  have h₁ := Finset.card_union_le (F∪Q) (Finset.univ.image loc)
  have h₂ := Finset.card_union_le F Q
  have h₃ := Finset.card_image_le (f:=loc) (s:=Finset.univ)
  simp only [Finset.card_univ,Fintype.card_fin] at h₃
  omega

def embed (loc : Fin d → X) (F Q : Finset X) : Fin (alphabet loc F Q).length ↪ X where
  toFun := (alphabet loc F Q).get
  inj' := by
    intro i j h
    apply Fin.ext
    have hh := congrArg (fun x=>List.idxOf x (alphabet loc F Q)) h
    simpa only [List.get_idxOf (alphabet_nodup loc F Q)] using hh

def index (loc : Fin d → X) (F Q : Finset X) (x : X) (h : x∈alphabet loc F Q) :
    Fin (alphabet loc F Q).length := ⟨List.idxOf x _,List.idxOf_lt_length_iff.mpr h⟩

@[simp] lemma embed_index (loc : Fin d → X) (F Q : Finset X) (x : X) (h) :
    embed loc F Q (index loc F Q x h)=x := List.getElem_idxOf _

def located (loc : Fin d → X) (F Q : Finset X) (j : Fin d) : Fin (alphabet loc F Q).length :=
  index loc F Q (loc j) ((mem_alphabet loc F Q _).mpr (Or.inr (Or.inr ⟨j,rfl⟩)))

@[simp] lemma embed_located (loc : Fin d → X) (F Q : Finset X) (j : Fin d) :
    embed loc F Q (located loc F Q j)=loc j := embed_index ..

def select (loc : Fin d → X) (F Q S : Finset X) : Finset (Fin (alphabet loc F Q).length) :=
  Finset.univ.filter (fun i=>embed loc F Q i∈S)

@[simp] lemma mem_select (loc : Fin d → X) (F Q S : Finset X) (i) :
    i∈select loc F Q S ↔ embed loc F Q i∈S := by simp [select]

lemma image_select (loc : Fin d → X) (F Q S : Finset X)
    (hS : ∀ x∈S,x∈alphabet loc F Q) : (select loc F Q S).image (embed loc F Q)=S := by
  ext x
  simp only [Finset.mem_image,mem_select]
  constructor
  · rintro ⟨i,hi,rfl⟩; exact hi
  · intro hx
    refine ⟨index loc F Q x (hS x hx),?_,embed_index ..⟩
    simpa only [embed_index] using hx

lemma select_cover (loc : Fin d → X) (F Q : Finset X) :
    select loc F Q Q ⊆ select loc F Q F ∪ select loc F Q (Q\F) := by
  intro i hi
  simp only [mem_select,Finset.mem_union,Finset.mem_sdiff] at *
  tauto

@[instance_reducible] noncomputable def metric [PseudoMetricSpace X]
    (loc : Fin d → X) (F Q : Finset X) : PseudoMetricSpace (Fin (alphabet loc F Q).length) :=
  PseudoMetricSpace.induced (embed loc F Q) inferInstance

def rows (loc : Fin d → X) (F Q : Finset X) (distance : X → Fin d → ℚ) :
    Fin (alphabet loc F Q).length → Fin d → ℚ := fun i j=>distance (embed loc F Q i) j

def complete (loc : Fin d → X) (distance : X → Fin d → ℚ) (F : Finset X) (v z lam : ℚ)
    (Q : Finset X) : List X :=
  (RationalPhase.completion (rows loc F Q distance) (select loc F Q F) v z lam
    (select loc F Q Q)).map (embed loc F Q)

def continuation (loc : Fin d → X) (distance : X → Fin d → ℚ) (F : Finset X) (v lam : ℚ)
    (q n : ℕ) (Q : Finset X) : List (List X) :=
  (CanonicalMergeCrossing.continuation (rows loc F Q distance) (select loc F Q F) v lam q n
    (select loc F Q Q)).map (List.map (embed loc F Q))

variable [PseudoMetricSpace X]

lemma complete_spec (loc : Fin d → X) (distance : X → Fin d → ℚ)
    (hd : ∀ f j,(distance f j:ℝ)=dist f (loc j)) (F B Q : Finset X) (v z lam : ℚ)
    (hv : (0:ℝ)<(v:ℝ)) (hv1 : (v:ℝ)<1/6) (hz : (0:ℝ)≤(z:ℝ)) (hQ : Q⊆F∪B) :
    Valid loc F B Q v z lam 0 (complete loc distance F v z lam Q) ∧
      (∀ i∈complete loc distance F v z lam Q,i∈F) ∧
      (complete loc distance F v z lam Q).length ≤ F.card := by
  let := metric loc F Q
  have he : ∀ a b,dist (embed loc F Q a) (embed loc F Q b)=dist a b := fun _ _=>rfl
  have hrows : ∀ f j,((rows loc F Q distance) f j:ℝ)=dist f (located loc F Q j) := by
    intro f j
    change (distance (embed loc F Q f) j:ℝ)=dist (embed loc F Q f) (embed loc F Q (located loc F Q j))
    rw [embed_located,hd]
  have hF : (select loc F Q F).image (embed loc F Q)=F :=
    image_select loc F Q F (fun x hx=>(mem_alphabet loc F Q x).mpr (Or.inl hx))
  have hQQ : (select loc F Q Q).image (embed loc F Q)=Q :=
    image_select loc F Q Q (fun x hx=>(mem_alphabet loc F Q x).mpr (Or.inr (Or.inl hx)))
  have hB : (select loc F Q (Q\F)).image (embed loc F Q)=Q\F :=
    image_select loc F Q (Q\F) (fun x hx=>(mem_alphabet loc F Q x).mpr
      (Or.inr (Or.inl (Finset.mem_sdiff.mp hx).1)))
  obtain ⟨hh,hr,hl⟩ := RationalPhase.completion_spec (located loc F Q) (rows loc F Q distance)
    hrows (select loc F Q F) (select loc F Q (Q\F)) (select loc F Q Q) v z lam hv hv1 hz
    (select_cover loc F Q)
  have hm := HistoryIsometry.valid_map (embed loc F Q) he _ _ _ _ _ _ _ _ _ hh
  simp only [embed_located,hF,hQQ,hB] at hm
  have hsub : Q\F⊆B := by
    intro x hx
    rcases Finset.mem_sdiff.mp hx with ⟨hx,hn⟩
    exact (Finset.mem_union.mp (hQ hx)).resolve_left hn
  refine ⟨⟨PhaseMergeSurgery.prefix_free_mono hm.1 hsub,hm.2⟩,?_,?_⟩
  · intro i hi
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi
    exact (mem_select ..).mp (hr j hj)
  · unfold complete
    rw [List.length_map]
    have hc : (select loc F Q F).card=F.card :=
      (Finset.card_image_of_injective (select loc F Q F) (embed loc F Q).injective).symm.trans (congrArg Finset.card hF)
    exact hl.trans_eq hc

lemma continuation_spec (loc : Fin d → X) (distance : X → Fin d → ℚ)
    (hd : ∀ f j,(distance f j:ℝ)=dist f (loc j)) (F B Q : Finset X) (v lam : ℚ)
    (hv : (0:ℝ)<(v:ℝ)) (hv1 : (v:ℝ)<1/6) (q n : ℕ) (hQ : Q⊆F∪B) :
    Runs loc F B Q v lam q n (continuation loc distance F v lam q n Q) := by
  let := metric loc F Q
  have he : ∀ a b,dist (embed loc F Q a) (embed loc F Q b)=dist a b := fun _ _=>rfl
  have hrows : ∀ f j,((rows loc F Q distance) f j:ℝ)=dist f (located loc F Q j) := by
    intro f j
    change (distance (embed loc F Q f) j:ℝ)=dist (embed loc F Q f) (embed loc F Q (located loc F Q j))
    rw [embed_located,hd]
  have hF : (select loc F Q F).image (embed loc F Q)=F :=
    image_select loc F Q F (fun x hx=>(mem_alphabet loc F Q x).mpr (Or.inl hx))
  have hQQ : (select loc F Q Q).image (embed loc F Q)=Q :=
    image_select loc F Q Q (fun x hx=>(mem_alphabet loc F Q x).mpr (Or.inr (Or.inl hx)))
  have hB : (select loc F Q (Q\F)).image (embed loc F Q)=Q\F :=
    image_select loc F Q (Q\F) (fun x hx=>(mem_alphabet loc F Q x).mpr
      (Or.inr (Or.inl (Finset.mem_sdiff.mp hx).1)))
  obtain ⟨hl,hh,hr⟩ := CanonicalMergeCrossing.continuation_spec (located loc F Q)
    (rows loc F Q distance) hrows (select loc F Q F) (select loc F Q (Q\F))
    (select loc F Q Q) v lam hv hv1 q n (select_cover loc F Q)
  have hm := HistoryIsometry.history_map (embed loc F Q) he _ _ _ _ _ _ _ _ _ hh
  simp only [embed_located,hF,hQQ,hB] at hm
  have hsub : Q\F⊆B := by
    intro x hx
    rcases Finset.mem_sdiff.mp hx with ⟨hx,hn⟩
    exact (Finset.mem_union.mp (hQ hx)).resolve_left hn
  apply Runs.mono_free (B:=Q\F) _ hsub
  refine ⟨?_,hm,?_⟩
  · simpa only [continuation,List.length_map] using hl
  · intro H hH i hi
    obtain ⟨G,hG,rfl⟩ := List.mem_map.mp hH
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi
    exact (mem_select ..).mp (hr G hG j hj)

 theorem correct_completion (loc : Fin d → X) (distance : X → Fin d → ℚ)
    (hd : ∀ f j,(distance f j:ℝ)=dist f (loc j)) (F : Finset X) (v z lam : ℚ)
    (hv : (0:ℝ)<(v:ℝ)) (hv1 : (v:ℝ)<1/6) (hz : (0:ℝ)≤(z:ℝ)) :
    CanonicalMergePath.CorrectCompletion loc F v z lam (complete loc distance F v z lam) := by
  intro B Q hQ
  have hh := complete_spec loc distance hd F B Q v z lam hv hv1 hz hQ
  exact ⟨hh.1,hh.2.1⟩

end MetricKMedianRecovery.FiniteLabelContinuation

end OAI
