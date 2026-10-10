import OAI.Combinatorics.HadwigerCounterexample.MatrixRankCounting
import OAI.Combinatorics.HadwigerCounterexample.CoordinateBlocks
import OAI.Combinatorics.HadwigerCounterexample.MomentLabelSupport

namespace OAI

/-! # Mixer Conditions -/

noncomputable section
namespace HadwigerCounterexample
open Matrix
open scoped BigOperators
variable {p : Shape} {n : ℕ}

abbrev MIdx (p : Shape) := Fin p.J × Comp p.g × Comp p.g
abbrev MArr (p : Shape) (n : ℕ) := MIdx p → Moment p n
abbrev Draw (p : Shape) (n : ℕ) :=
  MArr p n × MArr p n × (Fin p.b → Mat (Fin n) (Fin n))

def drawn (d : Draw p n) : Mixer p n where
  mixL i j k := d.1 (i,j,k)
  mixR i j k := d.2.1 (i,j,k)
  mixM := d.2.2

abbrev MOne (p : Shape) := (MIdx p × Bool)
abbrev MBits (p : Shape) := MOne p × Bool
def orderedM (m : Mixer p n) (i : MOne p) : Moment p n :=
  if i.2 then m.mixL i.1.1 i.1.2.1 i.1.2.2 else m.mixR i.1.1 i.1.2.1 i.1.2.2
def eitherM (b : Bool) {I : Type} (A : Mat I I) := if b then A else Aᵀ

def indexedSum (m : Mixer p n) (c : Vec (MBits p)) :=
  ∑ i : MBits p,c i • eitherM i.2 (orderedM m i.1)
def selfSum (m : Mixer p n) (f : Vec Bool) :=
  ∑ i : Bool,f i • eitherM i (selfM p n m.mixM)

def blockRank (d : Block p.g) (s t : Label p.b) (A : Moment p n) :=
  (pullM (blockRay p n s d) (blockRay p n t d) A).rank

def binaryGood (m : Mixer p n) :=
  ∀ s t : Label p.b,s≠t →
    (∀ (c : Vec (MBits p)) (b : Vec Bool),c ≠ 0 →
      n ≤ 5*blockRank Block.Z s t (indexedSum m c + selfSum m b)) ∧
    (∀ b : Vec Bool, b≠0 → n ≤ 5*blockRank Block.sharp s t (selfSum m b))

/-- Matrix on a point's v coordinates for Tmix(x,atom_l). -/
def qmix (m : Mixer p n) (x : Profile p n) (l : Tag p.g) : Moment p n :=
  ∑ j : Fin p.J, ∑ f : TagStar l, ∑ e : Comp p.g,
    (liftM (m.mixL j e f.val)ᵀ (m.mixR j e f.val)ᵀ (x e) +
      liftM (m.mixL j f.val e) (m.mixR j f.val e) (x e))

theorem Tmix_atom (m : Mixer p n) (x : Profile p n) (s : Label p.b)
    (z : Base p.g n) (l : Tag p.g) :
    Tmix m x (atom p l s z)=mpair (qmix m x l) (mom p s z) := by
  classical
  let v (i) := atom p l s z i
  let q := mom p s z
  have h (f : Comp p.g → Moment p n →ₗ[F] F) :
      ∑ e, f e (v e) = ∑ e : TagStar l, f e.val q := by
    let g e := f e q
    have he :
        ∑ e, f e (v e) = ∑ e ∈ Finset.univ.filter (fun e => inc e l),g e := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun i _ => ?_
      unfold v
      by_cases h : inc i l <;> simp [atom_def,h,q,g]
    rw [he]
    exact Finset.sum_subtype _ (by simp) g
  let L j a b := liftM (m.mixL j a b) (m.mixR j a b)
  let R j a b := liftM (m.mixL j a b)ᵀ (m.mixR j a b)ᵀ
  have hh (j : Fin p.J) :
      ∑ e, ∑ f, mpair (x e) (L j e f (v f)) =
        ∑ f : TagStar l, ∑ e, mpair (R j e f.val (x e)) q := by
    have he (e : Comp p.g) (f) : mpair (x e) (L j e f (v f)) =
          mpair (R j e f (x e)) (v f) := mpair_liftM _ _ _ _
    simp_rw [he]
    rw [Finset.sum_comm]
    let F f := ∑ e, mpair (R j e f (x e))
    specialize h F
    simpa only [F,LinearMap.sum_apply] using h
  have hh' (j : Fin p.J) :
      ∑ f, ∑ e, mpair (v f) (L j f e (x e)) =
        ∑ f : TagStar l, ∑ e, mpair (L j f.val e (x e)) q := by
    have he (e f : Comp p.g) : mpair (v f) (L j f e (x e))=mpair (L j f e (x e)) (v f) :=
      mpair_comm _ _
    simp_rw [he]
    let F f := ∑ e, mpair (L j f e (x e))
    specialize h F
    simpa only [F,LinearMap.sum_apply] using h
  change (∑ j, ∑ e, ∑ f, mpair (x e) (L j e f (v f)))+
    (∑ j, ∑ f, ∑ e,mpair (v f) (L j f e (x e))) = _
  simp_rw [hh,hh']
  simp only [qmix,mpair_sum,mpair_add,Finset.sum_add_distrib]
  rfl

theorem qmix_rank (m : Mixer p n) (x : Profile p n) (l) :
    (qmix m x l).rank ≤ p.J*(p.g-1)*(2*totalRank x) := by
  let W := 2*totalRank x
  let F (j : Fin p.J) (f : TagStar l) (e : Comp p.g) :=
    liftM (m.mixL j e f.val)ᵀ (m.mixR j e f.val)ᵀ (x e)+
    liftM (m.mixL j f.val e) (m.mixR j f.val e) (x e)
  have hh (j : Fin p.J) (f : TagStar l) : (∑ e, F j f e).rank ≤ W := by
    have hi (e : Comp p.g) : (F j f e).rank ≤ 2*(x e).rank := by
      unfold F; rw [two_mul]
      exact (mrk_add_le ..).trans (Nat.add_le_add (rank_lift_le ..) (rank_lift_le ..))
    refine (mrk_sum_le Finset.univ _).trans ((Finset.sum_le_sum fun i _ => hi i).trans_eq ?_)
    rw [←Finset.mul_sum]; rfl
  have hj j :
      (∑ f : TagStar l,∑ e,F j f e).rank ≤ (p.g-1)*W := by
    refine (mrk_sum_le Finset.univ _).trans ((Finset.sum_le_sum fun i _ => hh j i).trans_eq ?_)
    simp only [Finset.sum_const,Finset.card_univ,card_star,nsmul_eq_mul]; simp
  refine (mrk_sum_le Finset.univ _).trans ((Finset.sum_le_sum fun i _ => hj i).trans_eq ?_)
  simp [W,mul_assoc]

def unaryGood (m : Mixer p n) (K s0 : ℕ) :=
  ∀ (x : Profile p n) (l : Tag p.g) (s : Label p.b), totalRank x ≤ K → totalRank x > 0 →
    2*(p.J-s0) ≤ blockRank Block.Z s s (qmix m x l + (qmix m x l)ᵀ)

end HadwigerCounterexample

end

end OAI
