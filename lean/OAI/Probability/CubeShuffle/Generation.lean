import OAI.Probability.CubeShuffle.PairRouting
import OAI.RepresentationTheory.FiniteUnitary.Sampling

namespace OAI

namespace CubeShuffle.UnitaryFinite

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

lemma sampleOperator_palindrome (d : ℕ) (ρ : Representation ℂ (Equiv.Perm (Card d)) V)
    (hρ : IsUnitary ρ) :
    sampleOperator ρ (palindromePerm d)=
      sampleOperator ρ (fun ω => butterflyPerm d (decodeButterfly d ω))*
      (sampleOperator ρ (fun ω => butterflyPerm d (decodeButterfly d ω))).adjoint := by
  rw [←sampleOperator_inv ρ hρ,←sampleOperator_prod]
  rfl

end CubeShuffle.UnitaryFinite

namespace CubeShuffle
open scoped BigOperators Classical

def butterflyIdentity : (d : ℕ) → Butterfly d
  | 0 => ()
  | d+1 => (fun _ => false,fun _ => butterflyIdentity d)

lemma pairSwitch_false (d : ℕ) : pairSwitch (d := d) (fun _ => false)=1 := by
  apply Equiv.ext
  intro x
  change switchFun (fun _ => false) x=x
  simp [switchFun]

lemma childLift_one (d : ℕ) : childLift (d := d) (fun _ => 1)=1 := by
  ext x i
  simp [childLift]

lemma butterflyIdentity_perm (d : ℕ) : butterflyPerm d (butterflyIdentity d)=1 := by
  induction d with
  | zero => rfl
  | succ d ih => simp only [butterflyIdentity,butterflyPerm,ih,pairSwitch_false,childLift_one,mul_one]

noncomputable def childInjection (d : ℕ) (b : Bool) : Equiv.Perm (Card d) →* Equiv.Perm (Card (d+1)) where
  toFun p := childLift (fun c => if c=b then p else 1)
  map_one' := by simpa only [ite_self] using childLift_one d
  map_mul' p q := by
    rw [childLift_mul]
    congr 1
    funext c
    split_ifs <;> simp

lemma childInjection_swap (d : ℕ) (b : Bool) (u v : Card d) :
    childInjection d b (Equiv.swap u v)=Equiv.swap (Fin.cons b u) (Fin.cons b v) := by
  apply Equiv.ext
  intro x
  obtain ⟨c,w,rfl⟩ : ∃ c w, x=Fin.cons c w := ⟨x 0,Fin.tail x,(Fin.cons_self_tail x).symm⟩
  change (Fin.cons c ((if c=b then Equiv.swap u v else 1) w) : Card (d+1))=_
  by_cases hc : c=b
  · subst c
    simp only [↓reduceIte]
    rw [Equiv.swap_apply_def]
    split_ifs with h₁ h₂
    · subst w; simp
    · subst w; simp
    · rw [Equiv.swap_apply_of_ne_of_ne]
      · exact fun h => h₁ (by simpa using congrArg Fin.tail h)
      · exact fun h => h₂ (by simpa using congrArg Fin.tail h)
  · rw [ite_eq_right hc,Equiv.Perm.one_apply,Equiv.swap_apply_of_ne_of_ne]
    · intro h; exact hc (by simpa using congrArg (fun z => z 0) h)
    · intro h; exact hc (by simpa using congrArg (fun z => z 0) h)

lemma pairSwitch_single (d : ℕ) (u : Card d) :
    pairSwitch (fun v => decide (v=u))=Equiv.swap (Fin.cons false u) (Fin.cons true u) := by
  apply Equiv.ext
  intro x
  obtain ⟨c,w,rfl⟩ : ∃ c w, x=Fin.cons c w := ⟨x 0,Fin.tail x,(Fin.cons_self_tail x).symm⟩
  change switchFun (fun v => decide (v=u)) (Fin.cons c w)=_
  by_cases h : w=u
  · subst w
    cases c <;> simp [switchFun]
  · have ha : (Fin.cons c w : Card (d+1))≠Fin.cons false u := fun he => h (by simpa using congrArg Fin.tail he)
    have hb : (Fin.cons c w : Card (d+1))≠Fin.cons true u := fun he => h (by simpa using congrArg Fin.tail he)
    simp [switchFun,h,Equiv.swap_apply_of_ne_of_ne ha hb]

/-- Every genuine butterfly outcome generates the full symmetric group. -/
theorem butterfly_generates (d : ℕ) (H : Subgroup (Equiv.Perm (Card d)))
    (hH : ∀ ω : Butterfly d, butterflyPerm d ω∈H) : H=⊤ := by
  induction d with
  | zero =>
    apply top_unique
    intro p _
    have hp : p=1 := Subsingleton.elim _ _
    rw [hp]
    exact H.one_mem
  | succ d ih =>
    have hchild (b : Bool) (p : Equiv.Perm (Card d)) : childInjection d b p∈H := by
      have hc : H.comap (childInjection d b)=⊤ := by
        apply ih
        intro ω
        change childLift (fun c => if c=b then butterflyPerm d ω else 1)∈H
        have h := hH ((fun _ => false),fun c => if c=b then ω else butterflyIdentity d)
        simpa only [butterflyPerm,pairSwitch_false,one_mul,apply_ite,butterflyIdentity_perm] using h
      have hp : p∈H.comap (childInjection d b) := by rw [hc]; trivial
      exact hp
    have hpair (u : Card d) : Equiv.swap (Fin.cons false u) (Fin.cons true u)∈H := by
      rw [←pairSwitch_single]
      have h := hH ((fun v => decide (v=u)),fun _ => butterflyIdentity d)
      simpa only [butterflyPerm,butterflyIdentity_perm,childLift_one,mul_one] using h
    have hswap (x y : Card (d+1)) : Equiv.swap x y∈H := by
      have ht (a b : Bool) (u : Card d) : Equiv.swap (Fin.cons a u) (Fin.cons b u)∈H := by
        cases a <;> cases b
        · rw [Equiv.swap_self]; exact H.one_mem
        · exact hpair _
        · rw [Equiv.swap_comm]; exact hpair _
        · rw [Equiv.swap_self]; exact H.one_mem
      have h₁ : Equiv.swap x (Fin.cons (y 0) (Fin.tail x))∈H := by
        convert ht (x 0) (y 0) (Fin.tail x) using 1
        rw [Fin.cons_self_tail]
      have h₂ := hchild (y 0) (Equiv.swap (Fin.tail x) (Fin.tail y))
      rw [childInjection_swap,Fin.cons_self_tail] at h₂
      exact SubmonoidClass.swap_mem_trans H h₁ h₂
    rw [eq_top_iff,←Equiv.Perm.closure_isSwap,Subgroup.closure_le]
    rintro _ ⟨x,y,_,rfl⟩
    exact hswap x y

lemma butterfly_closure (d : ℕ) : Subgroup.closure (Set.range (butterflyPerm d))=⊤ :=
  butterfly_generates d _ (fun ω => Subgroup.subset_closure ⟨ω,rfl⟩)

end CubeShuffle

namespace CubeShuffle
open scoped BigOperators Classical

lemma palindrome_identity (d : ℕ) : ∃ ω,palindromePerm d ω=1 := by
  refine ⟨((butterflyCoinEquiv d).symm (butterflyIdentity d),
    (butterflyCoinEquiv d).symm (butterflyIdentity d)),?_⟩
  exact mul_inv_cancel _

lemma palindrome_range_contains_butterfly (d : ℕ) (ω : Butterfly d) :
    ∃ ξ,palindromePerm d ξ=butterflyPerm d ω := by
  refine ⟨((butterflyCoinEquiv d).symm ω,(butterflyCoinEquiv d).symm (butterflyIdentity d)),?_⟩
  unfold palindromePerm
  have h (β : Butterfly d) : decodeButterfly d ((butterflyCoinEquiv d).symm β)=β :=
    (butterflyCoinEquiv d).apply_symm_apply β
  rw [h,h,butterflyIdentity_perm,show (1 : Equiv.Perm (Card d)).symm=1 from rfl,mul_one]

lemma palindrome_support_generates (d : ℕ) :
    Subgroup.closure {g | 0<sampleLaw (palindromePerm d) g}=⊤ := by
  apply butterfly_generates
  intro ω
  apply Subgroup.subset_closure
  exact (sampleLaw_pos_iff _ _).mpr (palindrome_range_contains_butterfly d ω)

noncomputable def palindromeMinorant (d : ℕ) :
    FiniteConvolution.Minorant (sampleLaw (palindromePerm d)) :=
  FiniteConvolution.minorant (sampleLaw_nonneg _) (sampleLaw_sum _)
    ((sampleLaw_pos_iff _ _).mpr (palindrome_identity d)) (palindrome_support_generates d)

noncomputable def blockGap (d : ℕ) : ℝ := UnitaryFinite.minorantGap (palindromeMinorant d)

lemma blockGap_pos (d : ℕ) : 0<blockGap d := UnitaryFinite.minorantGap_pos _
lemma blockGap_lt_one (d : ℕ) : blockGap d<1 := UnitaryFinite.minorantGap_lt_one _

/-- Strict fixed-size palindrome contraction is derived from its actual coins,
not assumed, and is uniform in the represented space. -/
theorem palindrome_off_invariants_gap (d : ℕ) {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ (Equiv.Perm (Card d)) V) (hρ : UnitaryFinite.IsUnitary ρ) :
    ‖UnitaryFinite.weightedOperator ρ (sampleLaw (palindromePerm d))-
      UnitaryFinite.uniformOperator ρ‖≤blockGap d := by
  apply UnitaryFinite.norm_off_invariants_le_gap ρ hρ _ (sampleLaw_sum _)
  apply sampleLaw_symmetric _ (Equiv.prodComm _ _)
  intro ω
  simp only [palindromePerm,mul_inv_rev]
  rfl

end CubeShuffle

end OAI
