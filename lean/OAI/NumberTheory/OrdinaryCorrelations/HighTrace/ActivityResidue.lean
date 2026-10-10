import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.Test

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace
open Finset Classical
variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h L ℓ n : ℕ}

lemma Specification.activity_residue (s : S.Specification D h L) (p : S.Index)
    (hp : (p:ℕ) ∈ s.primeSupport) (b : ℤ) (a : ZMod (p:ℕ)) (ha : s.ResidueTest p b a) :
    a+(b+s.offset (s.activity p hp):ℤ) = 0 := by
  unfold Specification.activity
  split_ifs with he
  · subst p
    simpa only [s.offset_zero,add_zero] using ha.1 rfl
  · exact ha.2 _ (Classical.choose_spec (((s.support_iff_extra_or_label p).mp hp).resolve_left he))

lemma attached_activity_comparison_residues (w : ClosedLine h ℓ)
    (a b : AttachedSpec w D L) (r : S.Index)
    (hr : (r:ℕ) ∈ a.spec.primeSupport)
    (hrt : (r:ℕ) ∣ b.spec.label b.spec.tailStart)
    (x : S.Residues) (ha : ∀ p, a.spec.ResidueTest p a.vertex (x p))
    (hb : ∀ p, b.spec.ResidueTest p b.vertex (x p)) :
    ((r:ℕ):ℤ) ∣ b.vertex-a.vertex+b.spec.offset b.spec.tailStart.castSucc-
      a.spec.offset (a.spec.activity r hr) := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
  have hi := a.spec.activity_residue r hr a.vertex (x r) (ha r)
  have hj := (hb r).2 b.spec.tailStart hrt
  push_cast at hi hj ⊢
  linear_combination hj-hi

namespace PrivateFamily.Test
variable {w : ClosedLine h ℓ} {F : PrivateFamily w D L n} {j : Fin n}

lemma holds_residues (t : F.Test j) (ht : t.Valid) (x : S.Residues)
    (hx : ∀ i p, (F.witness i).spec.ResidueTest p (F.witness i).vertex (x p)) :
    ((t.modulus:ℕ):ℤ) ∣ t.expression := by
  cases t with
  | extra => exact (F.witness j).spec.extra_div_suffix
  | tail q => exact (F.witness j).spec.extra_div_suffix
  | compare i q r hi =>
      exact attached_activity_comparison_residues w (F.witness i) (F.witness j) r hi ht.1 x (hx i) (hx j)

end PrivateFamily.Test

noncomputable def sortPrivateFamily (w : ClosedLine h ℓ) (s : Fin n → AttachedSpec w D L)
    (q : Fin n → S.Index) (hq : ∀ j, (q j:ℕ) ∈ (s j).spec.primeSupport)
    (hf : ∀ j, ¬S.IsFixed w (q j))
    (hp : ∀ i j, i≠j → (q i:ℕ) ∉ (s j).spec.primeSupport) : PrivateFamily w D L n where
  witness j := s (Tuple.sort (fun j => (s j).index) j)
  key j := q (Tuple.sort (fun j => (s j).index) j)
  key_mem _ := hq _
  key_free _ := hf _
  key_private _ _ hij := hp _ _ (fun he => hij ((Tuple.sort _).injective he))
  ordered := Tuple.monotone_sort (fun j : Fin n => (s j).index)

lemma sortPrivateFamily_witness (w : ClosedLine h ℓ) (s : Fin n → AttachedSpec w D L)
    (q : Fin n → S.Index) (hq : ∀ j, (q j:ℕ) ∈ (s j).spec.primeSupport)
    (hf : ∀ j, ¬S.IsFixed w (q j))
    (hp : ∀ i j, i≠j → (q i:ℕ) ∉ (s j).spec.primeSupport)
    (P : AttachedSpec w D L → Prop) (hP : ∀ j, P (s j)) :
    ∀ j, P ((sortPrivateFamily w s q hq hf hp).witness j) := by
  intro j
  exact hP ((Tuple.sort (fun j : Fin n => (s j).index)) j)

end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
