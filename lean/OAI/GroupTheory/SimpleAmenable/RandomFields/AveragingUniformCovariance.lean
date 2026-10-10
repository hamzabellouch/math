import Mathlib
import OAI.GroupTheory.SimpleAmenable.RandomFields.AveragingAffinePairs

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section AveragingUniformCovariance
open Classical

theorem flagAveragingMatrix_uniform_difference {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (g : polygonFullGroup a m) :
    ∃R C : ℝ,0 ≤ R ∧ 0 ≤ C ∧
      ∀(χ : (ℝ×ℝ) → ℝ), (∀x,χ x∈Set.Icc (0:ℝ) 1) →
      ∀(L ρ N r η κ : ℝ),0 ≤ L → 0<ρ → 0<N → 1≤r → 0<η → 0<κ → R ≤ κ/(r/N) →
      (∀x y,|χ x-χ y| ≤ L*(|x.1-y.1|+|x.2-y.2|)) →
      ∀z w : FlagSite a m D v,
      |flagAveragingMatrix χ ρ N r η κ z w-
        flagAveragingMatrix χ ρ N r η κ (flagSiteAction hD g z) (flagSiteAction hD g w)| ≤
        (C*(2*L+1/κ)/(ρ*η^2))/(N*r) := by
  obtain ⟨R,hR,hbranch⟩ := flagAveragingMatrix_common_branch (v:=v) hD g
  obtain ⟨C,hC,hcost⟩ := flagAffineData_cost_bound (v:=v) g
  refine ⟨R,C,hR,hC,fun χ hχ L ρ N r η κ hL hρ hN hr hη hκ hbound hLip z w => ?_⟩
  have hr₀ : 0<r := lt_of_lt_of_le zero_lt_one hr
  by_cases hm : flagAveragingMatrix χ ρ N r η κ z w ≠ 0 ∨
      flagAveragingMatrix χ ρ N r η κ (flagSiteAction hD g z) (flagSiteAction hD g w) ≠ 0
  · have hf := hbranch χ ρ N r η κ hN hr₀ hκ hbound z w hm
    have he := flagAveragingMatrix_chart_difference hD g z w hf χ hχ hL hρ hN hr₀ hη hκ hLip
    have hnum : 0 ≤ 2*L+r/κ := by positivity
    have hden : 0<N*(ρ*(r*η)^2) := by positivity
    have hn : 2*L+r/κ ≤ r*(2*L+1/κ) := by
      have hh := mul_nonneg hL (sub_nonneg.mpr hr)
      simp only [div_eq_mul_inv,one_mul]
      nlinarith
    calc
      _ ≤ affineConjugateCost a (flagAffineData g z.val.1 z.val.2).2*(2*L+r/κ)/(N*(ρ*(r*η)^2)) := he
      _ ≤ C*(2*L+r/κ)/(N*(ρ*(r*η)^2)) := by gcongr; exact hcost z.val
      _ ≤ C*(r*(2*L+1/κ))/(N*(ρ*(r*η)^2)) := by gcongr
      _ = _ := by field_simp
  · have hz : flagAveragingMatrix χ ρ N r η κ z w=0 := not_not.mp (fun h => hm (Or.inl h))
    have hw : flagAveragingMatrix χ ρ N r η κ (flagSiteAction hD g z) (flagSiteAction hD g w)=0 :=
      not_not.mp (fun h => hm (Or.inr h))
    rw [hz,hw,sub_self,abs_zero]
    positivity

end AveragingUniformCovariance

section AveragingSupportCounts
open Classical

theorem pair_card_of_row_bound {α β : Type*} (T : Finset (α×β)) {B : ℝ}
    (hB : ∀x∈T.image Prod.fst, ((T.filter (fun p => p.1=x)).image Prod.snd).card ≤ B) :
    (T.card:ℝ) ≤ (T.image Prod.fst).card*B := by
  have hrow (x : α) : ((T.filter (fun p => p.1=x)).image Prod.snd).card=
      (T.filter (fun p => p.1=x)).card := by
    apply Finset.card_image_of_injOn
    intro p hp q hq he
    exact Prod.ext ((Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm) he
  rw [Finset.card_eq_sum_card_image Prod.fst T,Nat.cast_sum]
  calc
    _ ≤ ∑x∈T.image Prod.fst,B := Finset.sum_le_sum (fun x hx => by rw [← hrow x]; exact hB x hx)
    _ = _ := by simp

theorem flagAveragingMatrix_support_card {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (χ : (ℝ×ℝ) → ℝ) {K : ℝ} (hK : 0<K) (hχ : ∀x,K ≤ ‖x‖ → χ x=0)
    (ρ κ : ℝ) {N r η : ℝ} (hN : 0<N) (hr : 0<r) (hη : 0<η)
    (T : Finset (FlagSite a m D v × FlagSite a m D v))
    (hT : ∀p∈T,flagAveragingMatrix χ ρ N r η κ p.1 p.2 ≠ 0) :
    (T.card:ℝ) ≤ (m*(2*(D:ℝ)^2*(N*K)+2)^2)*(4*(D:ℝ)^2*r*η+2)^2 := by
  have hrows : ((T.image Prod.fst).card:ℝ) ≤ m*(2*(D:ℝ)^2*(N*K)+2)^2 := by
    apply flagSiteBox_card_bound hD (mul_pos hN hK)
    intro z hz
    obtain ⟨⟨z,w⟩,hp,rfl⟩ := Finset.mem_image.mp hz
    have hcz : χ (scaledSiteConjugate N z)≠0 := fun h => hT (z,w) hp
      (flagAveragingMatrix_cutoff_left χ ρ N r η κ z w h)
    have hn : ‖scaledSiteConjugate N z‖ < K := lt_of_not_ge (fun he => hcz (hχ _ he))
    have hx := (norm_fst_le (scaledSiteConjugate N z)).trans_lt hn
    have hy := (norm_snd_le (scaledSiteConjugate N z)).trans_lt hn
    simp only [scaledSiteConjugate,Real.norm_eq_abs,abs_div,abs_of_pos hN] at hx hy
    exact ⟨by nlinarith [(div_lt_iff₀ hN).mp hx],by nlinarith [(div_lt_iff₀ hN).mp hy]⟩
  have hc := pair_card_of_row_bound T (B:=(4*(D:ℝ)^2*r*η+2)^2) (fun z _ => ?_)
  · exact hc.trans (mul_le_mul_of_nonneg_right hrows (sq_nonneg _))
  · apply flagAveragingMatrix_row_card hD χ ρ κ hN hr hη z
    intro w hw
    obtain ⟨⟨z',w⟩,hp,rfl⟩ := Finset.mem_image.mp hw
    have he : z'=z := (Finset.mem_filter.mp hp).2
    subst z'
    exact hT (z,w) (Finset.mem_filter.mp hp).1

theorem flagAveragingMatrix_support_quadratic {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (χ : (ℝ×ℝ) → ℝ) {K : ℝ} (hK : 0<K) (hχ : ∀x,K ≤ ‖x‖ → χ x=0)
    (ρ κ : ℝ) {N r η : ℝ} (hN : 1≤N) (hr : 1≤r) (hη : 0<η)
    (T : Finset (FlagSite a m D v × FlagSite a m D v))
    (hT : ∀p∈T,flagAveragingMatrix χ ρ N r η κ p.1 p.2 ≠ 0) :
    (T.card:ℝ) ≤ (m*(2*(D:ℝ)^2*K+2)^2*(4*(D:ℝ)^2*η+2)^2)*N^2*r^2 := by
  have hx : 2*(D:ℝ)^2*(N*K)+2 ≤ (2*(D:ℝ)^2*K+2)*N := by nlinarith
  have hy : 4*(D:ℝ)^2*r*η+2 ≤ (4*(D:ℝ)^2*η+2)*r := by nlinarith
  have hx₀ : 0 ≤ 2*(D:ℝ)^2*(N*K)+2 := by positivity
  have hy₀ : 0 ≤ 4*(D:ℝ)^2*r*η+2 := by positivity
  calc
    _ ≤ (m*(2*(D:ℝ)^2*(N*K)+2)^2)*(4*(D:ℝ)^2*r*η+2)^2 :=
      flagAveragingMatrix_support_card hD χ hK hχ ρ κ (lt_of_lt_of_le zero_lt_one hN)
        (lt_of_lt_of_le zero_lt_one hr) hη T hT
    _ ≤ (m*((2*(D:ℝ)^2*K+2)*N)^2)*((4*(D:ℝ)^2*η+2)*r)^2 := by gcongr
    _ = _ := by ring

theorem flagAveragingMatrix_difference_support {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (g : polygonFullGroup a m) (χ : (ℝ×ℝ) → ℝ) {K : ℝ} (hK : 0<K)
    (hχ : ∀x,K ≤ ‖x‖ → χ x=0) (ρ κ : ℝ) {N r η : ℝ}
    (hN : 1≤N) (hr : 1≤r) (hη : 0<η)
    (T : Finset (FlagSite a m D v × FlagSite a m D v))
    (hT : ∀p∈T,flagAveragingMatrix χ ρ N r η κ p.1 p.2-
      flagAveragingMatrix χ ρ N r η κ (flagSiteAction hD g p.1) (flagSiteAction hD g p.2) ≠ 0) :
    (T.card:ℝ) ≤ (2*m*(2*(D:ℝ)^2*K+2)^2*(4*(D:ℝ)^2*η+2)^2)*N^2*r^2 := by
  let U := T.filter (fun p => flagAveragingMatrix χ ρ N r η κ p.1 p.2 ≠ 0)
  let V := T.filter (fun p => flagAveragingMatrix χ ρ N r η κ (flagSiteAction hD g p.1) (flagSiteAction hD g p.2) ≠ 0)
  have he : T ⊆ U∪V := by
    intro p hp
    by_cases h : flagAveragingMatrix χ ρ N r η κ p.1 p.2 ≠ 0
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hp,h⟩)
    · apply Finset.mem_union_right
      apply Finset.mem_filter.mpr
      refine ⟨hp,fun h' => hT p hp ?_⟩
      rw [not_not.mp h,h',sub_self]
  have hu := flagAveragingMatrix_support_quadratic hD χ hK hχ ρ κ hN hr hη U
    (fun p hp => (Finset.mem_filter.mp hp).2)
  let e := (flagSitePermutation (v:=v) hD g).prodCongr (flagSitePermutation (v:=v) hD g)
  have hv := flagAveragingMatrix_support_quadratic hD χ hK hχ ρ κ hN hr hη (V.image e)
    (by intro p hp; obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp; exact (Finset.mem_filter.mp hq).2)
  rw [Finset.card_image_of_injective V e.injective] at hv
  have hn : (T.card:ℝ) ≤ U.card+V.card := by
    exact_mod_cast (Finset.card_le_card he).trans (Finset.card_union_le _ _)
  nlinarith

end AveragingSupportCounts

section FiniteCovarianceEnergy
open Classical

theorem finite_correlation_bound {α : Type*} (T : Finset α) (f g : α → ℝ)
    {A B H : ℝ} (hA : 0≤A) (hB : 0≤B)
    (hf : ∀x∈T,|f x|≤A) (hg : ∀x∈T,|g x|≤B)
    (hc : ∀S⊆T,(∀x∈S,f x≠0) → (S.card:ℝ)≤H) :
    |∑x∈T,f x*g x| ≤ H*A*B := by
  let S := T.filter (fun x => f x≠0)
  have he : (∑x∈T,f x*g x)=∑x∈S,f x*g x := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro x hx hxS
    have hh : f x=0 := by simpa [S,hx] using hxS
    simp [hh]
  rw [he]
  calc
    _ ≤ ∑x∈S,|f x*g x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑_x∈S,A*B := Finset.sum_le_sum (fun x hx => by
      rw [abs_mul]
      exact mul_le_mul (hf x (Finset.mem_filter.mp hx).1)
        (hg x (Finset.mem_filter.mp hx).1) (abs_nonneg _) hA)
    _ = (S.card:ℝ)*A*B := by simp; ring
    _ ≤ H*A*B := by
      have hh := hc S (Finset.filter_subset _ _) (fun x hx => (Finset.mem_filter.mp hx).2)
      gcongr

theorem finite_half_geometric_sum (I : Finset ℕ) :
    ∑i∈I,(1/2:ℝ)^i ≤ 2 := by
  have hi : I ⊆ Finset.range (I.sup id+1) := by
    intro i hi
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f:=id) hi))
  calc
    _ ≤ ∑i∈Finset.range (I.sup id+1),(1/2:ℝ)^i :=
      Finset.sum_le_sum_of_subset_of_nonneg hi (fun _ _ _ => by positivity)
    _ ≤ 2 := by
      have h := geom_sum_Ico_le_of_lt_one (m:=0) (n:=I.sup id+1)
        (show (0:ℝ) ≤ 1/2 by norm_num) (show (1/2:ℝ)<1 by norm_num)
      norm_num at h ⊢
      exact h

theorem finite_dyadic_row (I : Finset ℕ) (i : ℕ) :
    ∑j∈I,(1/2:ℝ)^(Nat.dist i j) ≤ 4 := by
  let J := I.filter (fun j => j ≤ i)
  let K := I.filter (fun j => ¬j ≤ i)
  have hJ : Set.InjOn (Nat.dist i) J := by
    intro j hj k hk he
    have hj' := (Finset.mem_filter.mp hj).2
    have hk' := (Finset.mem_filter.mp hk).2
    rw [Nat.dist_eq_sub_of_le_right hj',Nat.dist_eq_sub_of_le_right hk'] at he
    omega
  have hK : Set.InjOn (Nat.dist i) K := by
    intro j hj k hk he
    have hj' : i ≤ j := by have := (Finset.mem_filter.mp hj).2; omega
    have hk' : i ≤ k := by have := (Finset.mem_filter.mp hk).2; omega
    rw [Nat.dist_eq_sub_of_le hj',Nat.dist_eq_sub_of_le hk'] at he
    omega
  have hj : ∑j∈J,(1/2:ℝ)^(Nat.dist i j) ≤ 2 := by
    rw [← Finset.sum_image hJ]
    exact finite_half_geometric_sum _
  have hk : ∑j∈K,(1/2:ℝ)^(Nat.dist i j) ≤ 2 := by
    rw [← Finset.sum_image hK]
    exact finite_half_geometric_sum _
  have he := Finset.sum_filter_add_sum_filter_not I (fun j => j ≤ i) (fun j => (1/2:ℝ)^(Nat.dist i j))
  change (∑j∈J,_) + (∑j∈K,_) = _ at he
  linarith

theorem finite_dyadic_energy {α : Type*} (T : Finset α) (I : Finset ℕ)
    (d : ℕ → α → ℝ) {C : ℝ} (hC : 0≤C)
    (hc : ∀i∈I,∀j∈I,i ≤ j → |∑x∈T,d i x*d j x| ≤ C*((2:ℝ)^i/(2:ℝ)^j))
    (w : ℝ) :
    ∑x∈T,(w*∑i∈I,d i x)^2 ≤ 4*C*(I.card:ℝ)*w^2 := by
  have he (i j : ℕ) (hi : i∈I) (hj : j∈I) :
      ∑x∈T,d i x*d j x ≤ C*(1/2:ℝ)^(Nat.dist i j) := by
    have aux (i j : ℕ) (hij : i ≤ j) : (2:ℝ)^i/(2:ℝ)^j=(1/2:ℝ)^(Nat.dist i j) := by
      rw [Nat.dist_eq_sub_of_le hij,div_pow,one_pow]
      have hh : (2:ℝ)^j=(2:ℝ)^i*(2:ℝ)^(j-i) := by
        rw [← pow_add,Nat.add_sub_of_le hij]
      rw [hh]
      field_simp
    by_cases hij : i ≤ j
    · exact (le_abs_self _).trans ((hc i hi j hj hij).trans_eq (by rw [aux i j hij]))
    · have hji : j ≤ i := by omega
      have h := (le_abs_self _).trans (hc j hj i hi hji)
      simpa only [mul_comm, Nat.dist_comm,aux j i hji] using h
  have hsum : ∑i∈I,∑j∈I,∑x∈T,d i x*d j x ≤ 4*C*(I.card:ℝ) := by
    calc
      _ ≤ ∑i∈I,∑j∈I,C*(1/2:ℝ)^(Nat.dist i j) :=
        Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun j hj => he i j hi hj))
      _ = ∑i∈I,C*(∑j∈I,(1/2:ℝ)^(Nat.dist i j)) := by simp_rw [Finset.mul_sum]
      _ ≤ ∑_i∈I,C*4 := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (finite_dyadic_row I i) hC)
      _ = _ := by simp; ring
  have hid : (∑x∈T,(w*∑i∈I,d i x)^2)=w^2*(∑i∈I,∑j∈I,∑x∈T,d i x*d j x) := by
    simp_rw [mul_pow,pow_two,Finset.sum_mul_sum]
    rw [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_comm]
  rw [hid]
  nlinarith [mul_le_mul_of_nonneg_left hsum (sq_nonneg w)]

end FiniteCovarianceEnergy

end SimpleAmenable
end
end

end OAI
