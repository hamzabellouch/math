import OAI.Combinatorics.HadwigerCounterexample.FixedPositionTests

namespace OAI

/-! # Full Template Comparison -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Function LinearMap
open scoped BigOperators
variable {p : Shape} {n N : ℕ} {I J A B : Type} [Fintype I] [DecidableEq I]

theorem ab_cut (p : Prop) (x : ℝ) (hx : |x|≤1) : |ind p*x|≤1 := by
  classical
  by_cases h : p
  · rwa [ind_one h,one_mul]
  rw [ind_zero h,zero_mul]; norm_num

theorem lift_window [Fintype A] [Fintype B] {u : Wgt A} (hu : IsLaw u)
    (v : Wgt B) (r : Wgt (A×B)) (s : Wgt A) (g : A→ Wgt B)
    (hr : ∀ i, r i = s i.1*g i.1 i.2) (hs : ∀ i, |s i|≤1) (ε : ℝ)
    (hh : ∀ i, |avg v (g i)| ≤ ε) : |avg (pairW u v) r|≤ ε := by
  rw [pairW_avg]
  simp_rw [hr,avg_mul']
  apply (abs_avg_le hu.nz).trans
  exact hu.avg_le (fun i => by
    rw [abs_mul]; exact (mul_le_mul (hs _) (hh _) (abs_nonneg _) zero_le_one).trans_eq (one_mul _))

namespace Template
variable (v : Template p I)

set_option maxHeartbeats 800000 in
theorem patched_board (v : Template p I) (j : I) (q : I→ F) (a : AtomKey (p:=p) (v.t j) N→ J)
    (B : J → Wgt (Keys (p:=p) (v.beyond j).t N)) (ε : ℝ)
    (h : ∀ i, shadowed (v.beyond j) (v.boundTail j q) (B i) ε) :
    shadowed v q (patched v j a B) ε := by
  classical
  intro f hf
  let t:=v.beyond j; let Q:=v.boundTail j q
  let E := chairK v j N
  let F (x : Keys (p:=p) v.t N) :=
    v.curtain q (v.patched j a B) x * prodW f x
  let s (x : AtomKey (p:=p) (v.t j) N) := ind (ownOne p _ (q j) x)*f j x
  let g (x : AtomKey (p:=p) (v.t j) N) : Localist t N := fun i z=> ind (v.bolts x z)*f i.val z
  let G x (y : Keys (p:=p) t.t N) := curtain t Q (B (a x)) y * prodW (g x) y
  have he k : (F ∘ E.symm) k=s k.1 * G k.1 k.2 := by
    obtain ⟨k,rfl⟩ := E.surjective k
    simp only [Function.comp_apply,Equiv.symm_apply_apply]
    unfold F curtain
    rw [bolts_split v j,chair_split _ _ j]; simp only [ind_and,ind_all]
    change _ * v.patched _ _ _ k * (f j (k j)* _)=s (k j)*G (k j) (E k).2
    unfold s G patched curtain g
    unfold prodW
    rw [Finset.prod_mul_distrib]
    exact (show ∀ (a b c d e f : ℝ), a*(b*c)*d*(e*f)=(a*e)*(c*d*(b*f)) from by intro a b c d e f; ring) _ _ _ _ _ _
  have hh (x) : |avg unif (G x)|≤ε := h (a x) _ (fun i y=>ab_cut _ _ (hf _ _))
  have hz (x) : |s x|≤1 := ab_cut _ _ (hf _ _)
  have ht : mapW unif E= pairW unif unif := by rw [←pair_unif,unif_equiv]
  have hl := lift_window unif_law unif _ _ _ he hz ε hh
  rw [←ht,mapW_avg] at hl
  simp only [Function.comp_apply,Equiv.symm_apply_apply] at hl; exact hl

set_option maxHeartbeats 800000 in
theorem patched_exceed (v : Template p I) (j : I) (q : I→F) (a : AtomKey (p:=p) (v.t j) N→J)
    (B : J → Wgt (Keys (p:=p) (v.beyond j).t N)) (ε : ℝ)
    (w : I→Wgt (Knobs p.g n)) (hw : ∀ i,IsLaw (w i))
    (s : Script p I) (m : Mixer p n) (o : UnitType p n N)
    (h : ∀ i,¬ exceeds (v.beyond j) (v.boundTail j q) (B i) (scriptTail s j)
      m (fun i => w i.val) ε o) :
    ¬ exceeds v q (patched v j a B) s m w ε o := by
  classical
  rintro ⟨f,hf,hZ⟩
  let x' := patched v j a B
  apply not_lt_of_ge _ hZ
  change |astonish v q x' s m w f o|≤ε
  rw [astonish_val]
  let v' := v.beyond j; let Q := v.boundTail j q
  let E := chairI v j n
  let R := scriptTail s j
  let U (i : Inputs p n I) := ind (earns v s m q o i)*x' (v.resultKey o i)*prodW f i
  let K := Knobs p.g n
  let x (z : K) := nib v o j z
  let g (i : K) (t : Aside j) (z : K) := ind (v.lintel j m s o i t z)*f t.val z
  let C (i) := ind (ownOne p _ (q j) (x i))*f j i
  let G i (y : Inputs p n (Aside j)) :=
    ind (earns v' R m Q o y)*B (a (x i)) (v'.resultKey o y)*prodW (g i) y
  have he k : (U ∘ E.symm) k=C k.1*G k.1 k.2 := by
    obtain ⟨k,rfl⟩ := E.surjective k
    simp only [Function.comp_apply,Equiv.symm_apply_apply]
    unfold U
    rw [earns_split v j,chair_split _ _ j]; simp only [ind_and,ind_all]
    unfold x' patched; rw [key_split]
    unfold C G g prodW
    rw [Finset.prod_mul_distrib]
    dsimp only [x,E,v',R,chairI,chair]
    change _ * B (a (nib v o j (k j))) _ * _ = _
    unfold nib
    dsimp only [Q,Equiv.piSplitAt,Equiv.coe_fn_mk]
    ring
  let W := prodW (fun i:Aside j=> w i.val)
  have hh (i) : |avg W (G i)|≤ ε := by
    have hz (k z) : |g i k z|≤1 := ab_cut _ _ (hf _ _)
    have hb : |astonish v' Q (B (a (x i))) R m (fun i=>w i.val) (g i) o|≤ε :=
      le_of_not_gt (fun hb=>h (a (x i)) ⟨g i,hz,hb⟩)
    rw [astonish_val] at hb; exact hb
  have hC i : |C i|≤1 := ab_cut _ _ (hf _ _)
  have ht : mapW (prodW w) E=pairW (w j) W := chair_weight w j
  have hz := lift_window (hw j) W _ _ _ he hC ε hh
  rw [←ht,mapW_avg] at hz
  simp only [Function.comp_apply,Equiv.symm_apply_apply] at hz
  exact hz

end Template
end HadwigerCounterexample

end

end OAI
