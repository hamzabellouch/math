import OAI.Combinatorics.HadwigerCounterexample.NominalPointArrays

namespace OAI

/-! # Synthetic Slice Comparison -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module LinearMap Function Finset
open scoped BigOperators
variable {p : Shape} {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable {n N : ℕ}

abbrev Display (p : Shape) (I : Type) (N : ℕ) := Comp p.g → Rack I N
def displayLaw (p : Shape) (I : Type) [Fintype I] [DecidableEq I] (N : ℕ) (G : Mat I I) :
    Wgt (Display p I N) := prodW (fun (_:Comp p.g) => unifOn (gramGood G))

theorem display_law (p : Shape) (G : Mat I I) (N : ℕ) (hN : 2*num I-(N:ℝ)≤ -1) :
    IsLaw (displayLaw p I N G) := by
  have hU : num I + num I-num (Fin N) ≤ -1 := by
    rw [← two_mul]; simpa only [num,Fintype.card_fin] using hN
  have hh := gram_norm_quarter G hU
  have ht : IsLaw (unifOn (gramGood G (U:=Fin N))) := by
    rw [←on_unif]; exact on_law unif_law.nz ((div_pos (bp_pos _) (by norm_num : 0<(4:ℝ))).trans_le hh)
  exact prodW_law (fun i : Comp p.g => ht)

def drill (p : Shape) (A : Mat (Row p n) I) (o : Orient p n N) : Display p I N :=
  fun i => peer p A A (o i)

theorem drill_law (p : Shape) {A : Mat (Row p n) I} (h : Injective A.mulVec)
    (m : Mixer p n) (hN : 2*num (Full p n)<N) :
    mapW (raw m N) (drill p A) = displayLaw p I N (pullM A A (selfM p n m.mixM)) := by
  classical
  unfold raw drill displayLaw
  let w := rawC m N
  have hh := mapW_repeat (fun (_ : Comp p.g)=>w) (fun i=>peer p A A (N:=N))
  rw [peer_cap _ _ hN h h] at hh
  exact hh

def drStage (p : Shape) (I : Type) : Route (Comp p.g × I) (Comp p.g) := Prod.fst

def drQuery (A : Mat (Row p n) I) : NomQuery p n (drStage p I) :=
  fun j => A.submatrix _root_.id (fun i : Port (drStage p I) j => i.val.2)

omit [DecidableEq I] in
theorem drill_view (p : Shape) {A : Mat (Row p n) I} (o : Orient p n N) :
    drill p A o= relay (Comp p.g) I N
      (peekR p (drStage p I) (drQuery A) (drQuery A) o) := by
  funext i; apply Prod.ext <;> rfl

theorem bloom_incision (p : Shape) (n : ℕ) (x : J→I→ Knobs p.g n)
    (l : Tag p.g) (s : Label p.b) (f : Flavor p.g)
    (h : bloom p x) (a : J) :
    Injective (incision p l s f (x a)).mulVec := by
  classical
  let M := incision p l s f (x a); let T:= freeNet p x
  let g := Prod.mk a (β:=I)
  have he (i : I) (j) : M (emptySel,some (Block.Z,j)) i=T j (g i) := by
    change point _ _ _ _=_
    rw [point_base_eval]
    exact ite_eq_left (Flavor.keepZ ..)
  intro y z hy
  refine inject_column_slice T h (show Injective g from fun i j h=>congrArg Prod.snd h) ?_
  funext i
  have hh:= congr_fun hy (emptySel,some (Block.Z,i))
  change ∑ j:I,M _ _*_=∑ j:I, M _ _*_ at hh
  simp_rw [he] at hh; exact hh
theorem bloom_drill (p : Shape) (n : ℕ) (x : J→I→ Knobs p.g n)
    (l : Tag p.g) (s : Label p.b) (f : Flavor p.g)
    (h : bloom p x) (i : Comp p.g) :
    Injective (pooled (fun j=> drQuery (incision p l s f (x j))) i).mulVec := by
  classical
  let r := fun y : J×(Comp p.g × I)=> (y.1,y.2.2)
  let T := tied (drStage p I) J
  have hr : Injective (fun a : Port T i=> r a.val) := by
    rintro ⟨⟨j,a,c⟩,ha⟩ ⟨⟨j',b,d⟩,hb⟩ hh
    change (j,c)=(j',d) at hh
    cases hh
    cases ha; cases hb; rfl
  refine ray_bloom (b:=r) _ _ h hr ?_
  intro j k
  change point p s (lit f l (x (r j.val).1 (r j.val).2)) (emptySel,some (Block.Z,k))=freeNet p x k (r j.val)
  rw [point_base_eval]; exact ite_eq_left (Flavor.keepZ ..)

def labGram (p : Shape) (l : Tag p.g) (s : Flavor p.g) (a : I→ Tickets p) : Mat I I :=
  Matrix.of (fun i j => tabGram p l s (a i) (a j))
end HadwigerCounterexample

end

end OAI
