import OAI.Combinatorics.HadwigerCounterexample.NumericalGradientTests

namespace OAI

/-! # Finite Table Enumeration -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Finset LinearMap Submodule Module Function
open scoped BigOperators
variable {p : Shape} {n N : ℕ}
namespace StatusAnalysis
abbrev CouponDeck (p : Shape) {n} (a b : Plan p n) :=
  ∀ i : Place p,Mat (Fin (dim (tabSpace a i))) (Fin (dim (tabSpace b (flipZ p i))))
def nomen (p : Shape) {n} (a b : Plan p n) (v : Cross p n) : CouponDeck p a b :=
  fun i=>pullM (pack (tabSpace a i)) (pack (tabSpace b (flipZ p i))) (v i)

theorem nomen_fits (p : Shape) (n : ℕ) (a b : Plan p n) (x y : Cross p n)
    (h : nomen p a b x=nomen p a b y) :
    fitsTable a b x y := by
  intro i j hj k hk
  obtain ⟨u,rfl⟩: ∃ v, pack (tabSpace a i)*ᵥv=j := by
    exact (pack_mem_iff ..).mp hj
  obtain ⟨v,rfl⟩: ∃ v, pack (tabSpace b (flipZ p i))*ᵥv=k := (pack_mem_iff ..).mp hk
  simp_rw [← evmat_pull]; exact congrArg (fun t=>evmat t u v) (congr_fun h i)

instance deckFin (p : Shape) (n : ℕ) (a b : Plan p n) : Fintype (CouponDeck p a b) := by
  classical
  infer_instance

def deckMax (p : Shape) (K : ℕ) :=
  Fintype.card (Place p)*(2*(K+p.h))^2

theorem deck_cap (p : Shape) (n : ℕ) (K : ℕ)
    (a b : Plan p n) (h : planRank a ≤ K) (hg :planRank b ≤ K) :
    Fintype.card (CouponDeck p a b) ≤ 2^ deckMax p K := by
  classical
  have ht :
      dim (CouponDeck p a b)=∑ i:Place p,dim (tabSpace a i)*dim (tabSpace b (flipZ p i)) := by
    unfold CouponDeck dim; rw [Module.finrank_pi_fintype]
    refine Finset.sum_congr rfl fun i _=>?_
    rw [show Module.finrank F _ = _ from dim_mat (Fin (dim (tabSpace a i)))
      (Fin (dim (tabSpace b (flipZ p i)))),Fintype.card_fin,Fintype.card_fin]
  have he (i) : dim (tabSpace a i)*dim (tabSpace b (flipZ p i)) ≤ (2*(K+p.h))^2 := by
    rw [pow_two]; exact Nat.mul_le_mul ((table_dim ..).trans (by omega)) ((table_dim ..).trans
      (by omega))
  have hi : dim (CouponDeck p a b) ≤ deckMax p K := ht ▸
    (Finset.sum_le_sum (fun i _=>he i)).trans_eq (by rw [Finset.sum_const]; exact
      (by simp [deckMax]))
  have hh := card_space (CouponDeck p a b)
  have hx : (↑(Fintype.card (CouponDeck p a b)) : ℝ)≤2^deckMax p K := hh.le.trans
    ((bp_le (by exact_mod_cast hi : (dim (CouponDeck p a b):ℝ) ≤ deckMax p K)).trans_eq (bp_nat _))
  exact_mod_cast hx

theorem deck_cast (p : Shape) (n : ℕ) (K : ℕ)
    (a b : Plan p n) (h : planRank a ≤ K) (hg :planRank b ≤ K) :
    ∃ M : Fin (2^deckMax p K)→Cross p n,∀ v,∃ i,fitsTable a b (M i) v := by
  classical
  let A := CouponDeck p a b
  let f := nomen p a b
  choose w he using fun x : A =>
    show ∃ y:Cross p n,∀ z,f z=x → f y=x from (by
      by_cases h : ∃ z,f z=x
      · obtain ⟨z,hz⟩:=h; exact ⟨z,fun _ _=>hz⟩
      exact ⟨0,fun i hi=>(h ⟨i,hi⟩).elim⟩)
  let t := Fintype.card A
  let e := Fintype.equivFin A
  let g (x : Fin (2^deckMax p K)) := if h : x.val<t then w (e.symm ⟨x.val,h⟩) else 0
  have hk : t≤2^deckMax p K := deck_cap p n K a b h hg
  refine ⟨g,fun v=>?_⟩
  let i:=e (f v); let z:Fin (2^deckMax p K):= Fin.castLE hk i
  refine ⟨z,nomen_fits p n _ _ _ _ ?_⟩
  change f (g z)=f v
  unfold g; rw [dite_eq_left (show z.val<t from i.isLt)]
  exact (by change f (w (e.symm (e (f v))))=f v; rw [Equiv.symm_apply_apply]; exact he _ _ rfl)

theorem fits_flag (M T : Cross p n) (a b : Pin p n N) (x : UnitType p n N)
    (hf : fitsTable a.sp b.sp M T) (h : tableFlag a b T x) : tableFlag a b M x :=
  fun i j hj k hk=> (hf i j hj k (pin_le_table b.sp _ hk)).trans (h i j hj k hk)
end StatusAnalysis
end HadwigerCounterexample

end

end OAI
