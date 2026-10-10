import Mathlib
import OAI.Combinatorics.HoneycombBridges.Concatenation

namespace OAI

/-! Unique irreducible factorization of strict bridges. -/

noncomputable section
open scoped ENNReal
open Filter

namespace HoneycombActual

def bridgeProduct : List Bridge → Option Bridge
  | [] => none
  | b :: bs => some (match bridgeProduct bs with
    | none => b
    | some c => b.concat c)

@[simp] theorem bridgeProduct_nil : bridgeProduct [] = none := rfl
@[simp] theorem bridgeProduct_singleton (b : Bridge) : bridgeProduct [b] = some b := rfl

@[simp] theorem bridgeProduct_eq_none_iff (bs : List Bridge) :
    bridgeProduct bs = none ↔ bs = [] := by
  cases bs <;> simp [bridgeProduct]

theorem bridgeProduct_exists_of_ne_nil (bs : List Bridge) (hn : bs ≠ []) :
    ∃ b : Bridge, bridgeProduct bs = some b := by
  cases he : bridgeProduct bs with
  | none => exact False.elim (hn ((bridgeProduct_eq_none_iff _).mp he))
  | some b => exact ⟨b, rfl⟩

theorem bridgeProduct_vertices {bs : List Bridge} {b : Bridge}
    (h : bridgeProduct bs = some b) : concatenateVertices bs = b.vertices := by
  induction bs generalizing b with
  | nil => simp at h
  | cons a as ih =>
    cases he : bridgeProduct as with
    | none =>
      have hn := (bridgeProduct_eq_none_iff _).mp he
      subst as
      have hb : a = b := by simpa using h
      subst b
      simp [concatenateVertices]
    | some c =>
      have hb : a.concat c = b := by simpa [bridgeProduct, he] using h
      rw [← hb, concatenateVertices, ih he]
      rfl

theorem bridgeProduct_of_vertices {bs : List Bridge} {b : Bridge}
    (h : concatenateVertices bs = b.vertices) : bridgeProduct bs = some b := by
  have hn : bs ≠ [] := by
    intro he
    subst bs
    exact b.vertices_ne_nil (by simpa [concatenateVertices] using h.symm)
  obtain ⟨c, hc⟩ := bridgeProduct_exists_of_ne_nil bs hn
  have he : c = b := Bridge.vertices_injective ((bridgeProduct_vertices hc).symm.trans h)
  simpa [he] using hc

theorem bridgeProduct_append {as bs : List Bridge} {a b : Bridge}
    (ha : bridgeProduct as = some a) (hb : bridgeProduct bs = some b) :
    bridgeProduct (as ++ bs) = some (a.concat b) := by
  induction as generalizing a with
  | nil => simp at ha
  | cons c cs ih =>
    cases hc : bridgeProduct cs with
    | none =>
      have hn := (bridgeProduct_eq_none_iff _).mp hc
      subst cs
      have he : c = a := by simpa using ha
      subst a
      simp [bridgeProduct, hb]
    | some d =>
      have he : c.concat d = a := by simpa [bridgeProduct, hc] using ha
      rw [← he]
      simp [bridgeProduct, ih hc, Bridge.concat_assoc]

theorem irreducible_factorization_exists (b : Bridge) :
    ∃ bs : List Bridge, bridgeProduct bs = some b ∧ ∀ a ∈ bs, a.Irreducible := by
  classical
  induction h : b.height using Nat.strong_induction_on generalizing b with
  | h n ih =>
    by_cases hb : b.Irreducible
    · exact ⟨[b], rfl, by simpa using hb⟩
    · simp only [Bridge.Irreducible, not_forall, not_not] at hb
      obtain ⟨r, hr, hrb, hc⟩ := hb
      obtain ⟨a, c, har, hac⟩ := b.split_at_of_crossingCount_one r hr hrb hc
      have hca : c.height < b.height := by
        have hp := a.height_pos
        have hh := congrArg Bridge.height hac
        simp only [Bridge.concat_height] at hh
        omega
      obtain ⟨as, has, hai⟩ := ih a.height (by omega) a rfl
      obtain ⟨cs, hcs, hci⟩ := ih c.height (by omega) c rfl
      refine ⟨as ++ cs, ?_, ?_⟩
      · rw [bridgeProduct_append has hcs, ← hac]
      · intro d hd
        exact (List.mem_append.mp hd).elim (hai d) (hci d)



theorem Bridge.concat_not_irreducible (a b : Bridge) : ¬ (a.concat b).Irreducible := by
  intro h
  have hb := b.height_pos
  exact h a.height a.height_pos (by simp; omega) (a.concat_crossing_at b)

theorem irreducible_product_unique (as bs : List Bridge)
    (ha : ∀ a ∈ as, a.Irreducible) (hb : ∀ b ∈ bs, b.Irreducible)
    (he : bridgeProduct as = bridgeProduct bs) : as = bs := by
  induction as generalizing bs with
  | nil =>
    have hnil : bs = [] := (bridgeProduct_eq_none_iff bs).mp he.symm
    exact hnil.symm
  | cons a as ih =>
    cases bs with
    | nil => simp [bridgeProduct] at he
    | cons c cs =>
      have hai : a.Irreducible := ha a (by simp)
      have hci : c.Irreducible := hb c (by simp)
      cases hpa : bridgeProduct as with
      | none =>
        have hn := (bridgeProduct_eq_none_iff as).mp hpa
        subst as
        cases hpc : bridgeProduct cs with
        | none =>
          have hn := (bridgeProduct_eq_none_iff cs).mp hpc
          subst cs
          have he' : a = c := by simpa using he
          simp [he']
        | some d =>
          have he' : a = c.concat d := by simpa [bridgeProduct, hpc] using he
          rw [he'] at hai
          exact False.elim ((c.concat_not_irreducible d) hai)
      | some b =>
        cases hpc : bridgeProduct cs with
        | none =>
          have hn := (bridgeProduct_eq_none_iff cs).mp hpc
          subst cs
          have he' : a.concat b = c := by simpa [bridgeProduct, hpa] using he
          rw [← he'] at hci
          exact False.elim ((a.concat_not_irreducible b) hci)
        | some d =>
          have he' : a.concat b = c.concat d := by simpa [bridgeProduct, hpa, hpc] using he
          have hh := Bridge.concat_irreducible_first_height_eq hai hci he'
          have hf := Bridge.concat_first_eq_of_height_eq he' hh
          subst c
          have ht : b = d := Bridge.concat_left_cancel he'
          have hp : bridgeProduct as = bridgeProduct cs := by rw [hpa, hpc, ht]
          have htail := ih cs (by intro z hz; exact ha z (List.mem_cons_of_mem _ hz))
            (by intro z hz; exact hb z (List.mem_cons_of_mem _ hz)) hp
          simp [htail]

theorem bridgeFactorization : BridgeFactorizationLaw := by
  intro b
  obtain ⟨bs, hbs, hbi⟩ := irreducible_factorization_exists b
  refine ⟨bs, ⟨hbi, bridgeProduct_vertices hbs⟩, ?_⟩
  intro cs hcs
  apply irreducible_product_unique cs bs hcs.1 hbi
  rw [bridgeProduct_of_vertices hcs.2, hbs]

end HoneycombActual

end

end OAI
