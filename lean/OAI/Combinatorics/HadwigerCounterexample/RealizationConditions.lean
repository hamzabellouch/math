import OAI.Combinatorics.HadwigerCounterexample.KeyDirections

namespace OAI

/-! # Realization Conditions -/

noncomputable section
namespace HadwigerCounterexample
open Matrix
open scoped BigOperators
variable {p : Shape} {n N : ℕ} {I : Type} [Fintype I]

namespace Volley
variable (v w : Volley p n I)

def legal (t : Tagging p I) := ∀ i : I, allows (t i) (v.par i)
def diagonalAt (i : I) := eta p n (mom p (v.sel i) (v.par i))
def bounded (w' : I→Bool) := ∀ (i j : Bool), 1≤ (v.shoots w' i j).card ∧
    (v.shoots w' i j).card ≤7

/-- Conditions for one orientation of roles, §5 (scalar recipe). -/
structure scalarRecipe (t : Tagging p I) (m : Mixer p n) (x : UnitType p n N) (S : Plan p n)
    (M : Cross p n) : Prop where
  summ (i j : Bool) : ∑ a ∈ v.shoots w.obj i j,v.diagonalAt a=1
  coupled (j : Bool) : ((innerP p x true)+role p n) (v.sumAt t w.obj true j) =
    ((innerP p x false)+role p n) (v.sumAt t w.obj false j)
  gradient (i j : Bool) (y : Profile p n) : y∈effective S i →
    grad m (v.sumAt t w.obj i j) y= contract p M i j y

def roleMatch (t : Tagging p I) :=
  ∀ i j, role p n (v.sumAt t w.obj i j)+ role p n (w.sumAt t v.obj j i)=1

def attackGrad (t : Tagging p I) (m : Mixer p n) (y : UnitType p n N) :=
  ∀ (a : I) (j : Bool),
    grad m (v.sumAt t w.obj (v.obj a) j) (v.atomAt t a) =
      if j=w.obj a then 0 else innerP p y (w.obj a) (w.atomAt t a)

def realized (t : Tagging p I) (m : Mixer p n) (M : Cross p n) :=
  ∀ i j, ∀ y ∈ Xspace p n, grad m (v.sumAt t w.obj i j) y=contract p M i j y

theorem shoots_swap (i j) : v.shoots w.obj i j=w.shoots v.obj j i := by
  ext; simp [shoots,and_comm]

theorem sum_share {t : Tagging p I} {x y : UnitType p n N} (h : v.keys t x=w.keys t y)
    (i j : Bool) : Uembed (onSide x i) (v.sumAt t w.obj i j)=
      Uembed (onSide y j) (w.sumAt t v.obj j i) := by
  classical
  unfold sumAt
  rw [map_sum,map_sum,← shoots_swap v w]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hi := (Finset.mem_filter.mp hk).2
  rw [← hi.1, ← hi.2]
  exact v.atom_share _ _ _ _ h k

theorem sum_mem {t : Tagging p I} (h : v.legal t) (f : I → Bool) (i j : Bool) :
    v.sumAt t f i j∈Xspace p n :=
  Submodule.sum_mem _ fun k _ => atom_mem _ (h k)

theorem realized_conflicts {t : Tagging p I} (m : Mixer p n)
    (x y : UnitType p n N) (hv : v.legal t) (hw : w.legal t)
    (hL : ∀ i, frameLaw m (onSide x i)) (hR : ∀ i, frameLaw m (onSide y i))
    (h : v.keys t x=w.keys t y) (hm : v.roleMatch w t)
    (hA : v.realized w t m (actual p x y)) (hB : w.realized v t m (actual p y x)) :
    (rawHoles m).conflict x y := by
  have hh i j : hole m (onSide x i) (onSide y j) := by
    refine ⟨hL i,hR j,v.sumAt t w.obj i j,w.sumAt t v.obj j i,
      v.sum_mem hv .., w.sum_mem hw .., v.sum_share _ h i j,fun q hq => ?_,fun q hq => ?_,hm i j⟩
    · rw [hA _ _ _ hq,contract_actual]; rfl
    · rw [hB _ _ _ hq,contract_actual]; rfl
  exact ⟨hh true true,hh true false,hh false true,hh false false⟩

end Volley

def scalarBlocks (p : Shape) {n} (M : Cross p n) (e : Place p) (i j : Bool) :=
  channelOut p M j e * IP p n i

theorem contract_val (p : Shape) {n} (M : Cross p n) (i j : Bool) (x : Profile p n) :
    contract p M i j x = ∑ e,mpair
      ((scalarBlocks p M (e,true) i j)ᵀ * scalarBlocks p M (e,false) i j) (x e) := by
  change ∑ e : Comp p.g, _ = _
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [mpair_liftM]
  simp only [liftM_def,transpose_transpose,scalarBlocks,transpose_mul,Matrix.mul_assoc]

theorem contract_scalars (A M : Cross p n) (h : scalarBlocks p A=scalarBlocks p M) (i j) :
    contract p A i j=contract p M i j := by
  refine LinearMap.ext fun v => ?_
  rw [contract_val,contract_val,h]
end HadwigerCounterexample

end

end OAI
