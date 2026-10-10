import OAI.Combinatorics.EditDistance.BinaryCode
import OAI.Combinatorics.EditDistance.RowSeparation

namespace OAI

/-!
# Contraction of arbitrary bit alignments to letter blocks
-/

namespace EditCode
open EditDistortion
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {A : Type*} {t k : ℕ}

def BlockPair (f g : Fin k → ℕ) (w i j : ℕ) : Prop :=
  ∀ r : ℕ, r < w → ∃ a : Fin k, f a = w*i+r ∧ g a = w*j+r

lemma BlockPair.symm {f g : Fin k → ℕ} {w i j : ℕ} (h : BlockPair f g w i j) :
    BlockPair g f w j i := by
  intro r hr
  obtain ⟨a,ha,hb⟩ := h r hr
  exact ⟨a,hb,ha⟩

lemma BlockPair.span {f g : Fin k → ℕ} {w i j : ℕ} (h : BlockPair f g w i j) :
    BlockSpan f g w i := ⟨w*j,h⟩

lemma pair_strict {f g : Fin k → ℕ} {w i j i' j' : ℕ}
    (hf : StrictMono f) (hg : StrictMono g) (hw : 0 < w)
    (h : BlockPair f g w i j) (h' : BlockPair f g w i' j') (hi : i < i') : j < j' := by
  obtain ⟨a,ha,hga⟩ := h 0 hw
  obtain ⟨b,hb,hgb⟩ := h' 0 hw
  have hab : a < b := hf.lt_iff_lt.mp (by simpa only [ha,hb,Nat.add_zero] using Nat.mul_lt_mul_of_pos_left hi hw)
  have := hg hab
  nlinarith

lemma pair_unique {f g : Fin k → ℕ} {w i j j' : ℕ}
    (hf : Function.Injective f) (hw : 0 < w)
    (h : BlockPair f g w i j) (h' : BlockPair f g w i j') : j = j' := by
  obtain ⟨a,ha,hga⟩ := h 0 hw
  obtain ⟨b,hb,hgb⟩ := h' 0 hw
  have hab : a = b := hf (ha.trans hb.symm)
  rw [hab] at hga
  nlinarith

lemma span_pair (label : A → Fin t → Bool) (x y : List A) (r s : ℕ)
    {f g : Fin k → ℕ}
    (hf : ∀ a, f a < (padded label x r).length)
    (hg : ∀ a, g a < (padded label y s).length)
    (heq : ∀ a, (padded label x r)[f a]'(hf a) = (padded label y s)[g a]'(hg a))
    (i : Fin x.length) (hi : BlockSpan f g (width t) i.val) :
    ∃ j : Fin y.length, BlockPair f g (width t) i.val j.val := by
  obtain ⟨q,hq⟩ := hi
  obtain ⟨a,ha,hga⟩ := hq 0 width_pos
  obtain ⟨b,hb,hgb⟩ := hq 1 (by unfold width; omega)
  have hqLen : q+1 < (padded label y s).length := by rw [←hgb]; exact hg b
  have hq₀ : (padded label y s)[q]'(by omega) = true := by
    have he := heq a
    have hv := padded_get_block label x r i ⟨0,width_pos⟩
    simp only [bit_zero,Nat.add_zero] at hv
    simpa only [ha,hga,Nat.add_zero,hv] using he.symm
  have hq₁ : (padded label y s)[q+1] = true := by
    have he := heq b
    have hv := padded_get_block label x r i ⟨1,by unfold width; omega⟩
    simp only [bit_one] at hv
    simpa only [hb,hgb,hv] using he.symm
  obtain ⟨j,hj⟩ := padded_delimiter label y s q hqLen hq₀ hq₁
  refine ⟨j,?_⟩
  intro a ha
  simpa only [hj] using hq a ha

lemma pair_letters (label : A → Fin t → Bool) (hinj : Function.Injective label)
    (x y : List A) (r s : ℕ) {f g : Fin k → ℕ}
    (hf : ∀ a, f a < (padded label x r).length)
    (hg : ∀ a, g a < (padded label y s).length)
    (heq : ∀ a, (padded label x r)[f a]'(hf a) = (padded label y s)[g a]'(hg a))
    (i : Fin x.length) (j : Fin y.length) (h : BlockPair f g (width t) i.val j.val) :
    x.get i = y.get j := by
  apply hinj
  funext v
  have hv : 2*v.val+3<width t := by unfold width; omega
  obtain ⟨a,ha,hb⟩ := h (2*v.val+3) hv
  have he := heq a
  have hx := padded_get_block label x r i ⟨2*v.val+3,hv⟩
  have hy := padded_get_block label y s j ⟨2*v.val+3,hv⟩
  simp only [ha,hb,hx,hy] at he
  simpa only [bit_label] using he

end EditCode

namespace EditCode
open EditDistortion
attribute [local instance] Classical.propDecidable
variable {A : Type*} {t k : ℕ}

theorem letter_loss_le (label : A → Fin t → Bool) (hinj : Function.Injective label)
    (x y : List A) (r s : ℕ) {f g : Fin k → ℕ}
    (hf : StrictMono f) (hg : StrictMono g)
    (hfB : ∀ a, f a < (padded label x r).length)
    (hgB : ∀ a, g a < (padded label y s).length)
    (heq : ∀ a, (padded label x r)[f a]'(hfB a) = (padded label y s)[g a]'(hgB a)) :
    indel x y ≤ 2 * (((padded label x r).length-k) + ((padded label y s).length-k)) := by
  classical
  let K := Finset.univ.filter (fun i : Fin x.length => BlockSpan f g (width t) i.val)
  let B := {i : Fin x.length // BlockSpan f g (width t) i.val}
  let C := {j : Fin y.length // BlockSpan g f (width t) j.val}
  have hpair (i : B) : ∃ j : Fin y.length, BlockPair f g (width t) i.val j.val :=
    span_pair label x y r s hfB hgB heq i.val i.property
  let next (i : B) : Fin y.length := (hpair i).choose
  have next_pair (i : B) : BlockPair f g (width t) i.val (next i).val := (hpair i).choose_spec
  let e : Fin K.card ↪o Fin x.length := K.orderEmbOfFin rfl
  have he (i : Fin K.card) : BlockSpan f g (width t) (e i).val :=
    (Finset.mem_filter.mp (K.orderEmbOfFin_mem rfl i)).2
  let q (i : Fin K.card) : Fin y.length := next ⟨e i,he i⟩
  have hq : StrictMono q := by
    intro i j hij
    exact pair_strict hf hg width_pos (next_pair ⟨e i,he i⟩) (next_pair ⟨e j,he j⟩)
      (e.strictMono hij)
  have hletter : ∀ i, x.get (e i) = y.get (q i) := by
    intro i
    exact pair_letters label hinj x y r s hfB hgB heq _ _ (next_pair ⟨e i,he i⟩)
  have hcost := indel_le_of_matching x.get y.get e (OrderEmbedding.ofStrictMono q hq) hletter
  simp only [List.ofFn_get] at hcost
  have hback (j : C) : ∃ i : Fin x.length, BlockPair g f (width t) j.val i.val :=
    span_pair label y x s r hgB hfB (fun a => (heq a).symm) j.val j.property
  let back (j : C) : B := ⟨(hback j).choose,(hback j).choose_spec.symm.span⟩
  have hbackinj : Function.Injective back := by
    intro j j' he
    have hh : (hback j).choose.val = (hback j').choose.val :=
      congrArg (fun i : B => i.val.val) he
    apply Subtype.ext
    apply Fin.ext
    apply pair_unique hf.injective width_pos (hback j).choose_spec.symm
    rw [hh]
    exact (hback j').choose_spec.symm
  have hcard := Fintype.card_le_of_injective back hbackinj
  have hcard' : (Finset.univ.filter (fun j : Fin y.length => BlockSpan g f (width t) j.val)).card ≤ K.card := by
    simpa only [B,C,Fintype.card_subtype,K] using hcard
  have hbadX := bad_blocks_le_loss hf hg width_pos hfB hgB
    (show width t * x.length ≤ (padded label x r).length by simp)
  have hbadY := bad_blocks_le_loss hg hf width_pos hgB hfB
    (show width t * y.length ≤ (padded label y s).length by simp)
  have hsplitX := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (fun i : Fin x.length => BlockSpan f g (width t) i.val)
  have hsplitY := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (fun j : Fin y.length => BlockSpan g f (width t) j.val)
  simp only [Finset.card_univ,Fintype.card_fin] at hsplitX hsplitY
  change K.card + _ = _ at hsplitX
  omega

theorem indel_code_lower (label : A → Fin t → Bool) (hinj : Function.Injective label)
    (x y : List A) (r s : ℕ) :
    indel x y ≤ 2 * indel (padded label x r) (padded label y s) := by
  obtain ⟨z,hx,hy,hcost⟩ := indel_matching (padded label x r) (padded label y s)
  obtain ⟨f,hf⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hx
  obtain ⟨g,hg⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hy
  have h := letter_loss_le label hinj x y r s
    (f := fun a => (f a).val) (g := fun a => (g a).val)
    (fun _ _ h => f.strictMono h) (fun _ _ h => g.strictMono h)
    (fun a => (f a).isLt) (fun a => (g a).isLt)
    (fun a => (hf a).symm.trans (hg a))
  have hzX := hx.length_le
  have hzY := hy.length_le
  have he : (padded label x r).length-z.length + ((padded label y s).length-z.length) =
      (padded label x r).length+(padded label y s).length-2*z.length := by omega
  rwa [he,←hcost] at h

end EditCode

end OAI
