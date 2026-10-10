import OAI.Algebra.OddKaplansky.OrderedGroup

namespace OAI

universe portUniverse1 portUniverse2 portUniverse3

section
namespace OddKaplansky.OrderedCosetCoordinates
noncomputable section
open scoped Classical BigOperators
variable {G : Type portUniverse1} [Group G] [Fintype G] [LinearOrder G] (S : Subgroup G)
local instance orderedCoordinatesDecidableEq : DecidableEq G := Classical.decEq G
def rep (q : G ⧸ S) : G := FiniteChoice.first (fun g : G => (g : G ⧸ S)=q) ⟨q.out,Quotient.out_eq' q⟩
lemma rep_mk (q : G ⧸ S) : ((rep S q : G) : G ⧸ S) = q := by
  unfold rep
  exact FiniteChoice.first_spec (fun g : G => (g : G ⧸ S)=q) ⟨q.out,Quotient.out_eq' q⟩
lemma rep_le (q : G ⧸ S) (g : G) (hg : (g : G ⧸ S)=q) : rep S q ≤ g := FiniteChoice.first_le _ _ g hg
lemma rep_injective : Function.Injective (rep S) := by
  intro q r h
  simpa only [rep_mk] using congrArg (fun g : G => (g : G ⧸ S)) h
@[instance_reducible]
def quotientOrder : LinearOrder (G ⧸ S) := LinearOrder.lift' (rep S) (rep_injective S)
lemma residue_mem (g : G) : (rep S (g : G ⧸ S))⁻¹*g ∈ S :=
  QuotientGroup.eq.mp (rep_mk S (g : G ⧸ S))
def residue (g : G) : S := ⟨_,residue_mem S g⟩
lemma reconstruct (g : G) : rep S (g : G ⧸ S) * residue S g = g := by simp [residue]
lemma mk_rep_mul (q : G ⧸ S) (s : S) : ((rep S q * (s : G) : G) : G ⧸ S) = q := by
  rw [QuotientGroup.mk_mul_of_mem _ s.property,rep_mk]
lemma residue_rep_mul (q : G ⧸ S) (s : S) : residue S (rep S q * s) = s := by
  apply Subtype.ext
  simp only [residue,mk_rep_mul]
  exact inv_mul_cancel_left _ _
def equiv : G ≃ (G ⧸ S) × S where
  toFun g := ((g : G ⧸ S),residue S g)
  invFun z := rep S z.1 * z.2
  left_inv := reconstruct S
  right_inv z := by ext <;> simp only [mk_rep_mul,residue_rep_mul]
lemma equiv_symm_apply (q : G ⧸ S) (s : S) : (equiv S).symm (q,s) = rep S q * s := rfl

lemma sum_right_invariant {A : Type portUniverse2} [AddCommMonoid A] (a : G → A)
    (ha : ∀ (s : S) (g : G), a (g*s) = a g) :
    ∑ g : G, a g = Fintype.card S • ∑ q : G ⧸ S, a (rep S q) := by
  rw [← Equiv.sum_comp (equiv S).symm a]
  simp only [Fintype.sum_prod_type,equiv_symm_apply,ha,Finset.sum_const,Finset.card_univ,← Finset.smul_sum]
lemma sum_left_invariant {A : Type portUniverse3} [AddCommMonoid A] (a : G → A)
    (ha : ∀ (s : S) (g : G), a (s*g) = a g) :
    ∑ g : G, a g = Fintype.card S • ∑ q : G ⧸ S, a (rep S q)⁻¹ := by
  have hh := sum_right_invariant S (fun g => a g⁻¹) (fun s g => by simpa only [mul_inv_rev,Subgroup.coe_inv] using ha s⁻¹ g⁻¹)
  have hi : (∑ g : G, a g⁻¹) = ∑ g : G, a g := Equiv.sum_comp (Equiv.inv G) a
  rw [hi] at hh
  exact hh
lemma coprime_order_of_sum (M : ℕ) (a : G → ZMod M) (hsum : ∑ g, a g = 1)
    (g : G) (hfix : ∀ x, a (g*x) = a x) : Nat.Coprime (orderOf g) M := by
  have hf : ∀ (s : Subgroup.zpowers g) (x : G), a (s*x) = a x := by
    intro s x
    obtain ⟨n,hn⟩ := s.property
    rw [← hn]
    have hnat (n : ℕ) : ∀ x, a (g^n*x)=a x := by
      induction n with
      | zero => intro x; simp
      | succ n ih => intro x; rw [pow_succ',mul_assoc,hfix,ih]
    cases n with
    | ofNat n => simpa only [Int.ofNat_eq_natCast,zpow_natCast] using hnat n x
    | negSucc n =>
      have h := hnat (n+1) ((g^(n+1))⁻¹ * x)
      simpa only [zpow_negSucc,← mul_assoc,mul_inv_cancel,one_mul] using h.symm
  have h := sum_left_invariant (Subgroup.zpowers g) a hf
  rw [hsum,Fintype.card_zpowers,nsmul_eq_mul] at h
  exact (ZMod.isUnit_iff_coprime _ _).mp (IsUnit.of_mul_eq_one _ h.symm)
lemma eq_one_of_power_and_sum (M : ℕ) (a : G → ZMod M) (hsum : ∑ g, a g = 1)
    (g : G) (hfix : ∀ x, a (g*x) = a x) (hpow : g^M=1) : g=1 :=
  orderOf_eq_one_iff.mp ((coprime_order_of_sum M a hsum g hfix).eq_one_of_dvd (orderOf_dvd_of_pow_eq_one hpow))
end
end OddKaplansky.OrderedCosetCoordinates

end

end OAI
