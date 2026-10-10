import OAI.NumberTheory.Ostmann.Construction.OffDiagonalParentCoprime

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Construction

theorem canonicalFrame_joined_valid_of_old_coprime
    (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ → ℕ) (giant : PrimeSource)
    (outside : List ℕ) (l p : ℕ)
    (x y : RemainingSample sources (Template.remainder (l+1) (Template.current seed l)) giant)
    (s : ℤ) (v w : AllowedFrequency V l)
    (u : SourceAssignment sources (Template.extracted (l+1) (Template.current seed l)))
    (hseed : ∀ q ∈ seed, ∀ j, q.role = .compensation j → 0 < j)
    (hp : 0 < p) (hs : s ≠ 0) (hsV : s.natAbs ≤ V (l+1))
    (hgiants : V (l+1) < x.1.val ∧ V (l+1) < y.1.val)
    (hlarge : ∀ q ∈ assignedSlots sources (Template.remainder (l+1) (Template.current seed l)) x.2,
      V (l+1) < q.value)
    (hx : (remainingState sources (Template.current seed l) (l+1) giant p u x v.val).Coprime outside)
    (hy : (remainingState sources (Template.current seed l) (l+1) giant p u y w.val).Coprime outside)
    (heq : joinedNumerator sources (Template.remainder (l+1) (Template.current seed l)) giant x y v.val w.val =
      s * ((assignedSlots sources (Template.extracted (l+1) (Template.current seed l)) u).map SmallSlot.value).prod * (p : ℤ)) :
    (canonicalFrame sources seed V l
      (joinedRemainingState sources (Template.remainder (l+1) (Template.current seed l)) giant x y s)
      v w u).Valid V outside l := by
  let T := Template.current seed l
  let R := Template.remainder (l+1) T
  let us := assignedSlots sources (Template.extracted (l+1) T) u
  let xs := assignedSlots sources R x.2
  let ys := assignedSlots sources R y.2
  let a := joinedRemainingState sources R giant x y s
  let ax := remainingState sources T (l+1) giant p u x v.val
  let ay := remainingState sources T (l+1) giant p u y w.val
  have hxperm : ax.small.Perm (us ++ xs) := Template.reinsert_perm (l+1) T us xs
    (assignedSlots_length _ _ _) (assignedSlots_length _ _ _)
  have hyperm : ay.small.Perm (us ++ ys) := Template.reinsert_perm (l+1) T us ys
    (assignedSlots_length _ _ _) (assignedSlots_length _ _ _)
  have hP : (halfProduct x.1.val xs).Coprime (halfProduct p us) :=
    (state_coprime_halves ax us xs outside hxperm hx).2.2
  have hxp : Nat.Prime x.1.val := giant.prime _ x.1.property
  have hyp : Nat.Prime y.1.val := giant.prime _ y.1.property
  have hxs : ∀ q ∈ xs, Nat.Prime q.value := assignedSlots_prime sources R x.2
  have hys : ∀ q ∈ ys, Nat.Prime q.value := assignedSlots_prime sources R y.2
  have hreversal : Arithmetic.reversalNumerator v.val w.val
      (halfProduct x.1.val xs : ℤ) (halfProduct y.1.val ys : ℤ) = s * (halfProduct p us : ℤ) := by
    change joinedNumerator sources R giant x y v.val w.val = _
    rw [heq]
    simp only [halfProduct,Nat.cast_mul]
    ring
  have hcross : (halfProduct x.1.val xs).Coprime (halfProduct y.1.val ys) :=
    reversal_sample_halves_coprime (halfProduct p us) x.1.val y.1.val xs ys v.val w.val s hs hxp hxs hP
      ⟨hsV.trans_lt hgiants.1,fun q hq => hsV.trans_lt (hlarge q hq)⟩ hreversal
  have hcop : a.Coprime outside := joined_pairwise_of_halves x.1.val y.1.val xs ys outside
    (remaining_half_pairwise ax us xs outside hxperm hx)
    (remaining_half_pairwise ay us ys outside hyperm hy) hcross
  have hpos : a.Positive := by
    intro q hq
    simp only [a,joinedRemainingState,State.values,List.mem_cons,List.map_append,List.mem_append] at hq
    rcases hq with rfl | rfl | hq | hq
    · exact hxp.pos
    · exact hyp.pos
    · obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hq
      exact (hxs z hz).pos
    · obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hq
      exact (hys z hz).pos
  have hprime : a.PrimeSmall := by
    intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hxs q hq
    · exact hys q hq
  have htemplate : a.TemplateAt (l+1) := by
    intro q hq j hrole
    rcases List.mem_append.mp hq with hq | hq
    · exact remaining_assigned_templateAt sources seed hseed l x.2 q hq j hrole
    · exact remaining_assigned_templateAt sources seed hseed l y.2 q hq j hrole
  have hpivot := reversalPivot_eq
    (joinedNumerator sources R giant x y v.val w.val) (us.map SmallSlot.value).prod p s
    (assignedSlots_product_pos sources (Template.extracted (l+1) T) u) hs heq
  rw [canonicalFrame_joined]
  rw [hpivot]
  change (⟨a,p,us,xs,ys,ax,ay⟩ : NodeFrame).Valid V outside l
  refine ⟨⟨hpos,hprime,htemplate,hcop,hs,hsV⟩,?_,?_⟩
  · exact ⟨History.prime_coprime_small_frequency hxp hs (hsV.trans_lt hgiants.1),
      History.prime_coprime_small_frequency hyp hs (hsV.trans_lt hgiants.2)⟩
  · exact ⟨hp,assignedSlots_extracted_roles sources T (l+1) u,List.Perm.refl _,
      rfl,rfl,rfl,rfl,hxperm,hyperm,heq⟩

theorem joinedRemainingState_giantGuard (sources : SourceFamily) (T : List SourceSlot)
    (giant : PrimeSource) (x y : RemainingSample sources T giant) (s : ℤ)
    {V : ℕ → ℕ} {outside : List ℕ} {l : ℕ} {h : History l} (hs : h.Supported V outside)
    (hgiants : ∀ j ≤ l, V j < x.1.val ∧ V j < y.1.val) :
    History.giantGuard (joinedRemainingState sources T giant x y s) h :=
  History.giantGuard_of_prime_bounds hs _ (giant.prime _ x.1.property)
    (giant.prime _ y.1.property) hgiants

end Ostmann.Construction

end

end OAI
