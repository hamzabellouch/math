import OAI.Combinatorics.HadwigerCounterexample.BasisConditioning

namespace OAI

/-! # Scalar Status Algebra -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Submodule Finset Function Module
open scoped BigOperators

namespace StatusAnalysis
abbrev Nodes := Bool
abbrev Grid := Nodes × Nodes
abbrev Cell (d : ℕ) := Vec (Fin d)

abbrev Par (d : ℕ) := F × Cell d
abbrev Whole (d : ℕ) := Par d × F

abbrev Signal (d e : ℕ) := F × Whole d × Whole e
abbrev View (d e : ℕ) := F × Par d × Par e
abbrev Question (d e : ℕ) := F × F × Cell d × Cell e
variable {d e : ℕ}

def view (d e : ℕ) : Signal d e→ₗ[F] View d e where
  toFun x := (x.1,x.2.1.1,x.2.2.1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
def testV (d e : ℕ) : View d e →ₗ[F] Question d e where
  toFun x := (x.1,x.2.1.1 + x.2.2.1,x.2.1.2,x.2.2.2)
  map_add' _ _ := Prod.ext rfl (Prod.ext (add_add_add_comm ..) rfl)
  map_smul' _ _ := Prod.ext rfl (Prod.ext (mul_add _ _ _).symm rfl)
def want (d e : ℕ) := testV d e ∘ₗ view d e

def couple (d : ℕ) : Whole d→ₗ[F] F where
  toFun x := x.1.1+x.2
  map_add' _ _ := add_add_add_comm ..
  map_smul' a _ := (mul_add a _ _).symm

def coverBase (V : Space (Signal d e)) := Surjective (view d e ∘ₗ V.subtype)
theorem testV_surj (d e : ℕ) : Surjective (testV d e) := by
  rintro ⟨a,b,x,y⟩
  exact ⟨(a,(b,x),(0,y)),Prod.ext rfl (Prod.ext (add_zero _) rfl)⟩
theorem coversFull {V : Space (Signal d e)} (h : coverBase V) : Surjective (want d e ∘ₗ V.subtype) :=
  (testV_surj _ _).comp h

abbrev Rates := Nodes→ℕ
abbrev Suite (A B : Rates) (i : Grid) := Signal (A i.1) (B i.2)
abbrev LedgerS (A B : Rates) (i : Grid) := Question (A i.1) (B i.2)
abbrev Cabinet (A B : Rates) := ∀ i, LedgerS A B i
abbrev Quota := Vec Nodes
abbrev Court (A B : Rates) := Cabinet A B × Quota × Quota
abbrev StatusSp (A B : Rates) := ∀ i,Space (Suite A B i)
variable {A B : Rates}

def separate (A B : Rates) (i : Grid) :
    Suite A B i →ₗ[F] Court A B :=
  (LinearMap.single F (LedgerS A B) i ∘ₗ want _ _).prod
    ((LinearMap.single F (fun _ : Bool=>F) i.2 ∘ₗ
      (couple (A i.1) ∘ₗ LinearMap.fst F _ _ ∘ₗ LinearMap.snd F _ _)).prod
     (LinearMap.single F (fun _ : Bool=>F) i.1 ∘ₗ
      (couple (B i.2) ∘ₗ LinearMap.snd F _ _ ∘ₗ LinearMap.snd F _ _)))

def speak (A B : Rates) :
    (∀ i,Suite A B i) →ₗ[F] Court A B := ∑ i:Grid,separate A B i ∘ₗ LinearMap.proj i

theorem speak_solo (A B : Rates) (i : Grid) (x : Suite A B i) :
    speak A B (Pi.single i x)=separate A B i x := by
  classical
  unfold speak; rw [LinearMap.sum_apply,sum_eq_single i]
  · rw [LinearMap.comp_apply]; change separate _ _ _ ((Pi.single i x : ∀ i, Suite A B i) i)=_
    rw [Pi.single_eq_same]
  · intro j _ hj; rw [LinearMap.comp_apply]
    change separate _ _ _ ((Pi.single i x : ∀ i, Suite A B i) j)=_
    rw [Pi.single_eq_of_ne hj,map_zero]
  simp

def scorecard (V : StatusSp A B) (T : Cabinet A B) :=
  ∃ v : ∀ i,Suite A B i,(∀ i,v i∈V i) ∧ speak A B v=(T,0)

structure Critic (A B : Rates) where
  alf : ∀ i : Grid, LedgerS A B i →ₗ[F] F
  altL : Quota
  altR : Quota
def Counter (g : Critic A B) (V : StatusSp A B) :=
  ∀ i:Grid,∀ v∈V i, g.alf i (want _ _ v) =
    g.altL i.2 * couple _ v.2.1 + g.altR i.1 * couple _ v.2.2

private theorem vanishes {M : Type} [AddCommGroup M] [Module F M] (V : Space M) {z}
    (h : z∉ V) :
    ∃ f:M→ₗ[F] F,f z ≠0 ∧ ∀ i∈V,f i=0 := by
  have he : V.mkQ z ≠0 := fun hg=>h ((Submodule.Quotient.mk_eq_zero V).mp hg)
  obtain ⟨f,hf⟩ := Module.Projective.exists_dual_ne_zero F he
  exact ⟨f ∘ₗ V.mkQ,hf,fun i hi =>by rw [LinearMap.comp_apply,show V.mkQ i=0 from
    (Submodule.Quotient.mk_eq_zero V).mpr hi,map_zero]⟩

set_option maxHeartbeats 800000 in
theorem counter_score (V : StatusSp A B) (T : Cabinet A B)
    (h : ¬scorecard V T) :
    ∃ g : Critic A B,Counter g V ∧ ∑ i,g.alf i (T i)≠0 := by
  classical
  let S := (Submodule.pi Set.univ V).map (speak A B)
  have ht : (T,(0 : Quota × Quota))∉ S := by
    rintro ⟨z,hz,he⟩
    exact h ⟨z,fun i => hz i (Set.mem_univ _),he⟩
  obtain ⟨f,hf,hx⟩ := vanishes S ht
  let g : Critic A B := {
    alf := fun i => f ∘ₗ LinearMap.inl F (Cabinet A B) _ ∘ₗ LinearMap.single F _ i
    altL := fun i=> f (0,Pi.single i 1,0)
    altR := fun i=> f (0,0,Pi.single i 1) }
  refine ⟨g,fun i v hv => ?_,?_⟩
  · have hi :
        f (separate A B i v)=0 := by
      apply hx
      refine ⟨Pi.single i v,?_,speak_solo A B i v⟩
      intro j _
      by_cases ht : j=i
      · subst j; rwa [Pi.single_eq_same]
      rw [Pi.single_eq_of_ne ht]; exact zero_mem _
    let a:= couple _ v.2.1
    let b:= couple _ v.2.2
    let Q:= want _ _ v
    have hh (a:F) (i:Bool) :
       (a • Pi.single i 1 : Quota)=Pi.single i a := by
      ext j; by_cases he:j=i <;> simp [he]
    have hz :
        separate A B i v =
        ( (Pi.single i Q : Cabinet A B),0) + (a • (0,Pi.single i.2 1,(0:Quota))+
          b • (0,(0:Quota),Pi.single i.1 1)) := by
      change ((Pi.single i Q:Cabinet A B),(Pi.single i.2 a:Quota),(Pi.single i.1 b:Quota))=_
      apply Prod.ext; simp
      apply Prod.ext <;> simp [hh]
    rw [hz,map_add,map_add,map_smul,map_smul] at hi
    change g.alf i Q+(a*g.altL i.2+b*g.altR i.1)=0 at hi
    change _=g.altL _ * a+g.altR _ * b
    rw [mul_comm _ a,mul_comm _ b]
    exact add_right_cancel (hi.trans (char_two _).symm)
  · have hh (i) : g.alf i (T i)=f ((Pi.single i (T i) : Cabinet A B),0) := rfl
    have ht : ∑ i:Grid, ((Pi.single i (T i) : Cabinet A B),(0 : Quota × Quota))=
        (T,0) := by
      apply Prod.ext
      · rw [Prod.fst_sum]; exact Finset.univ_sum_single _
      · simp only [Prod.snd_sum,Finset.sum_const_zero]
    simp_rw [hh, ← map_sum,ht]
    exact hf

theorem critic_nz (V : StatusSp A B) (T : Cabinet A B) (hV : ∀ i,coverBase (V i)) (g : Critic A B)
    (h : Counter g V) (hh : ∑ i,g.alf i (T i)≠0) : g.altL≠0 ∨ g.altR≠0 := by
  classical
  by_contra! hz
  apply hh; apply Finset.sum_eq_zero
  intro i _
  obtain ⟨⟨v,hv⟩,ht⟩ := coversFull (hV i) (T i)
  simpa only [show want (A i.1) (B i.2) v=T i from ht,hz.1,hz.2,Pi.zero_apply,zero_mul,add_zero]
    using h i v hv

end StatusAnalysis
end HadwigerCounterexample

end

end OAI
