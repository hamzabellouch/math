import OAI.Combinatorics.HadwigerCounterexample.MomentCoordinates

namespace OAI

/-! # Quadratic Testers -/

noncomputable section
namespace HadwigerCounterexample
open Matrix
open scoped BigOperators

theorem pair_outers {I J : Type} [Fintype I] [Fintype J] (x x' : Vec I) (y y' : Vec J) :
    mpair (vecMulVec x y) (vecMulVec x' y') =
      dotProduct x x' * dotProduct y y' := by
  simp only [mpair, dotProduct,vecMulVec_apply,LinearMap.coe_mk,AddHom.coe_mk,
    Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem mpair_sum {I J : Type} [Fintype I] [Fintype J] (m : Mat I J)
    {α : Type*} (s : Finset α) (f : α → Mat I J) :
    mpair (∑ i ∈ s, f i) m = ∑ i ∈ s, mpair (f i) m := by
  rw [mpair_comm,map_sum]
  exact Finset.sum_congr rfl fun i _ => mpair_comm _ _

theorem mpair_add {I J : Type} [Fintype I] [Fintype J] (A B M : Mat I J) :
    mpair (A+B) M = mpair A M + mpair B M := by rw [mpair_comm,map_add,mpair_comm M,mpair_comm M]

theorem mpair_smul {I J : Type} [Fintype I] [Fintype J] (b : F) (A M : Mat I J) :
    mpair (b • A) M = b * mpair A M := by rw [mpair_comm,map_smul,mpair_comm M, smul_eq_mul]

variable (p : Shape)

def pick (n : ℕ) (u : SelIdx p.b p.j) (d : Block p.g) (i : ℕ) : Ray p n :=
  if h : i < n then Pi.single (u,some (d,⟨i,h⟩)) 1 else 0

def readBit {n g} (z : Base g n) (d : Block g) (i : ℕ) : F :=
  if h : i < n then z (d,⟨i,h⟩) else 0

def testM (n : ℕ) (d : Block p.g) : Moment p n :=
  ∑ i : Fin p.r, vecMulVec (pick p n emptySel d (2*i.val))
    (pick p n emptySel d (2*i.val+1))

def etab (n) (d : Block p.g) : Moment p n →ₗ[F] F := mpair (testM p n d)

def test (n : ℕ) (d : Block p.g) (z z' : Base p.g n) : F :=
  ∑ i : Fin p.r, readBit z d (2*i.val) * readBit z' d (2*i.val+1)

theorem pick_point {n} (s) (z : Base p.g n) (u : SelIdx p.b p.j)
    (d : Block p.g) (i : ℕ) :
    dotProduct (pick p n u d i) (point p s z) = selV _ s u * readBit z d i := by
  by_cases hi : i < n
  · rw [pick,dite_eq_left hi,single_one_dotProduct,readBit,dite_eq_left hi]; rfl
  · rw [pick,dite_eq_right hi,zero_dotProduct, readBit,dite_eq_right hi,mul_zero]

theorem etab_point {n} (d : Block p.g) (s s') (z z' : Base p.g n) :
    etab p n d (vecMulVec (point p s z) (point p s' z')) = test p n d z z' := by
  unfold etab testM test
  simp only [mpair_sum,pair_outers,pick_point]
  simp [selV,emptySel]

theorem etab_disabled {n} {l d : Tag p.g} (h : ¬allowed d l) (t : Tag p.g)
    {m : Moment p n} (hm : m ∈ Wtag p n l) :
    etab p n (Block.O d t) m = 0 := by
  unfold Wtag at hm
  induction hm using Submodule.span_induction with
  | mem m hm =>
    obtain ⟨s,z,hz,rfl⟩ := hm
    rw [mom,etab_point]
    have h' (i : ℕ) : readBit z (Block.O d t) i = 0 := by
      simp [readBit,hz d t h]
    simp only [test,h',mul_zero,Finset.sum_const_zero]
  | zero => rw [map_zero]
  | add _ _ _ _ h g => rw [map_add,h,g,add_zero]
  | smul _ _ _ h => rw [map_smul,h,smul_zero]

/-- all O testers. -/
def etaO (n) : Moment p n →ₗ[F] F :=
  ∑ (d : Tag p.g), ∑ (t : Tag p.g), etab p n (Block.O d t)

def eta (n) : Moment p n →ₗ[F] F := etaO p n + etab p n Block.S

/-- a_t read on full ambient profile using allowed tags with partner d. -/
def roleT (n : ℕ) (t : Tag p.g) : Profile p n →ₗ[F] F :=
  ∑ (l : Tag p.g), ∑ d ∈ Finset.univ.filter (fun d => allowed d l),
    etab p n (Block.O d t) ∘ₗ getPair p n l d

theorem roleT_cut {n} (t : Tag p.g) (w : Tag p.g → Moment p n)
    (hw : ∀ i, w i ∈ Wtag p n i) :
    roleT p n t (cut p n w) =
      ∑ (l : Tag p.g), ∑ (d : Tag p.g), etab p n (Block.O d t) (w l) := by
  simp only [roleT,LinearMap.sum_apply,LinearMap.comp_apply,getPair_cut,map_add]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun d _ => ?_
  by_cases h : allowed d l
  · rw [ite_eq_left h,etab_disabled p (not_allowed d) t (hw d),add_zero]
  · rw [ite_eq_right h,etab_disabled p h t (hw l)]

def role (n : ℕ) := ∑ t : Tag p.g, roleT p n t

theorem role_cut {n} (w : Tag p.g → Moment p n) (hw : ∀ i,w i ∈ Wtag p n i) :
    role p n (cut p n w) = ∑ i, etaO p n (w i) := by
  simp only [role,LinearMap.sum_apply,roleT_cut _ _ _ hw]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_comm]
  simp only [etaO,LinearMap.sum_apply]

/-- b_t read on the full ambient profile. -/
def sharedT (n : ℕ) (t : Tag p.g) : Profile p n →ₗ[F] F :=
  ∑ (l : Tag p.g), etab p n Block.S ∘ₗ getPair p n l t

theorem sharedT_cut {n} (hg : Odd p.g) (t : Tag p.g) (w : Tag p.g → Moment p n) :
    sharedT p n t (cut p n w) =
      (∑ i, etab p n Block.S (w i)) + etab p n Block.S (w t) := by
  simp only [sharedT,LinearMap.sum_apply,LinearMap.comp_apply,getPair_cut,map_add,
    Finset.sum_add_distrib,Finset.sum_const, Finset.card_univ]
  simp [Tag,odd_smul_bit hg]

def sharpPick (n : ℕ) (a : Fin p.b) (i : Fin n) : Ray p n :=
  if h : 1 ≤ p.j then pick p n ⟨{a},by simp [h]⟩ Block.sharp i.val else 0

def sharpM (n : ℕ) (Y : Fin p.b → Mat (Fin n) (Fin n)) : Moment p n :=
  ∑ a : Fin p.b, ∑ i : Fin n, ∑ j : Fin n,
    Y a i j • (vecMulVec (sharpPick p n a i) (pick p n emptySel Block.sharp j.val) +
      vecMulVec (pick p n emptySel Block.sharp i.val) (sharpPick p n a j))

theorem sharpM_point {n} (hj : 1 ≤ p.j) (Y) (s s') (z z' : Base p.g n) :
    mpair (sharpM p n Y) (vecMulVec (point p s z) (point p s' z')) =
      ∑ a : Fin p.b, (s a + s' a) *
        evmat (Y a) (fun i => z (Block.sharp,i)) (fun i => z' (Block.sharp,i)) := by
  simp only [sharpM,mpair_sum,mpair_smul,mpair_add,pair_outers,
    sharpPick,dite_eq_left hj,pick_point,readBit,dite_eq_left (Fin.isLt _)]
  simp [selV,emptySel,evmat,dotProduct,mulVec,Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => ?_
  ring

def selfM (n) (Y : Fin p.b → Mat (Fin n) (Fin n)) : Moment p n :=
  ((∑ d : Tag p.g, ∑ t : Tag p.g, testM p n (Block.O d t)) +
    testM p n Block.S) + sharpM p n Y

theorem selfM_pair {n} (hj : 1 ≤ p.j) (Y) {m : Moment p n} (hm : m ∈ Wspace p n) :
    mpair (selfM p n Y) m = eta p n m := by
  unfold Wspace at hm
  induction hm using Submodule.span_induction with
  | mem m h =>
    obtain ⟨s,z,rfl⟩ := h
    simp only [selfM,mpair_sum,mpair_add,mom,sharpM_point p hj,char_two,zero_mul,
      Finset.sum_const_zero, add_zero,eta,etaO,etab,LinearMap.add_apply,
      LinearMap.sum_apply]
  | zero => simp only [map_zero]
  | add _ _ _ _ h g => rw [map_add,h,g,map_add]
  | smul _ _ _ h => rw [map_smul,h,map_smul]

end HadwigerCounterexample

end

end OAI
