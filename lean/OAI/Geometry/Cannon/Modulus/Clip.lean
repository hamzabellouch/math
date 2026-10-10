import Mathlib

namespace OAI

section
section
section
noncomputable section
section
section
section
section
section
section
section
section
section
section
section
section
section
open Set MeasureTheory
open scoped BigOperators

namespace CannonAnnular

theorem weighted_open_interval_cover {ι : Type*} [Fintype ι]
    (L U w : ι → ℝ) (a b c : ℝ) (hab : a ≤ b)
    (hLU : ∀ i, L i ≤ U i) (hw : ∀ i, 0 ≤ w i)
    (hcover : ∀ t ∈ Ioo a b,
      c ≤ ∑ i, (Icc (L i) (U i)).indicator (fun _ : ℝ => w i) t) :
    c * (b - a) ≤ ∑ i, w i * (U i - L i) := by
  have hint (l u v : ℝ) : Integrable ((Icc l u).indicator (fun _ : ℝ => v)) := by
    apply (integrable_indicator_iff measurableSet_Icc).mpr
    exact integrableOn_const (by simp [Real.volume_Icc])
  have hinta : Integrable ((Ioo a b).indicator (fun _ : ℝ => c)) := by
    apply (integrable_indicator_iff measurableSet_Ioo).mpr
    exact integrableOn_const (by simp [Real.volume_Ioo])
  have hle : (Ioo a b).indicator (fun _ : ℝ => c) ≤
      fun t => ∑ i, (Icc (L i) (U i)).indicator (fun _ : ℝ => w i) t := by
    intro t
    by_cases ht : t ∈ Ioo a b
    · simpa [Set.indicator_of_mem ht] using hcover t ht
    · rw [Set.indicator_of_notMem ht]
      exact Finset.sum_nonneg (fun i _ => Set.indicator_nonneg (fun _ _ => hw i) _)
  have hi := integral_mono hinta
    (integrable_finsetSum _ (fun i _ => hint (L i) (U i) (w i))) hle
  rw [integral_finsetSum _ (fun i _ => hint (L i) (U i) (w i))] at hi
  simpa only [integral_indicator_const _ measurableSet_Ioo,
    integral_indicator_const _ measurableSet_Icc, Measure.real,
    Real.volume_Ioo, Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.mpr hab),
    ENNReal.toReal_ofReal (sub_nonneg.mpr (hLU _)), smul_eq_mul, mul_comm] using hi

theorem interval_energy_cover {ι : Type*} [Fintype ι]
    (L U w : ι → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hLU : ∀ i, L i ≤ U i) (hw : ∀ i, 0 ≤ w i)
    (hcover : ∀ t ∈ Ioo a b,
      1 ≤ ∑ i, (Icc (L i) (U i)).indicator (fun _ : ℝ => w i) t) :
    (b - a)^2 ≤ (∑ i, (w i)^2) * (∑ i, (U i - L i)^2) := by
  have h := weighted_open_interval_cover L U w a b 1 hab hLU hw hcover
  simp only [one_mul] at h
  exact (pow_le_pow_left₀ (sub_nonneg.mpr hab) h 2).trans
    (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ w (fun i => U i - L i))

theorem overlap_energy {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (R : α → Finset β) (w : β → ℝ) (kr kc : ℕ)
    (hrow : ∀ i, (R i).card ≤ kr)
    (hcol : ∀ j, (Finset.univ.filter (fun i => j ∈ R i)).card ≤ kc) :
    (∑ i, (∑ j ∈ R i, w j)^2) ≤
      (kr : ℝ) * kc * (∑ j, (w j)^2) := by
  classical
  have hrowE (i : α) : (∑ j ∈ R i, w j)^2 ≤ (kr : ℝ) * (∑ j ∈ R i, (w j)^2) := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (R i) (fun _ => (1:ℝ)) w
    simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at h
    exact h.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hrow i)
      (Finset.sum_nonneg (fun j _ => sq_nonneg (w j))))
  have hswap : (∑ i, ∑ j ∈ R i, (w j)^2) =
      ∑ j, ((Finset.univ.filter (fun i => j ∈ R i)).card : ℝ) * (w j)^2 := by
    calc
      _ = ∑ i, ∑ j : β, if j ∈ R i then (w j)^2 else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [← Finset.sum_filter]
        simp
      _ = ∑ j, ∑ i ∈ Finset.univ.filter (fun i => j ∈ R i), (w j)^2 := by
        simp only [Finset.sum_filter]
        rw [Finset.sum_comm]
      _ = _ := by simp
  calc
    _ ≤ ∑ i, (kr : ℝ) * (∑ j ∈ R i, (w j)^2) := Finset.sum_le_sum (fun i _ => hrowE i)
    _ = (kr : ℝ) * (∑ i, ∑ j ∈ R i, (w j)^2) := (Finset.mul_sum ..).symm
    _ = (kr : ℝ) * (∑ j, ((Finset.univ.filter (fun i => j ∈ R i)).card : ℝ) * (w j)^2) := by rw [hswap]
    _ ≤ (kr : ℝ) * (∑ j, (kc : ℝ) * (w j)^2) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right
        (by exact_mod_cast hcol j) (sq_nonneg (w j)))
    _ = _ := by rw [← Finset.mul_sum]; ring

theorem annular_energy_transfer {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]
    (R : α → Finset β) (S : α → Finset γ) (ω : β → ℝ) (ρ : γ → ℝ)
    (L U : α → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hω : ∀ j, 0 ≤ ω j) (_hρ : ∀ j, 0 ≤ ρ j) (hLU : ∀ i, L i ≤ U i)
    (hlocal : ∀ i, U i - L i ≤ ∑ j ∈ S i, ρ j)
    (kr kc lr lc : ℕ)
    (hRrow : ∀ i, (R i).card ≤ kr)
    (hRcol : ∀ j, (Finset.univ.filter (fun i => j ∈ R i)).card ≤ kc)
    (hSrow : ∀ i, (S i).card ≤ lr)
    (hScol : ∀ j, (Finset.univ.filter (fun i => j ∈ S i)).card ≤ lc)
    (hcover : ∀ t ∈ Ioo a b,
      1 ≤ ∑ i, (Icc (L i) (U i)).indicator (fun _ : ℝ => ∑ j ∈ R i, ω j) t) :
    (b-a)^2 ≤ ((kr:ℝ)*kc*lr*lc) * (∑ j, (ω j)^2) * (∑ j, (ρ j)^2) := by
  have henergy := interval_energy_cover L U (fun i => ∑ j ∈ R i, ω j) a b hab hLU
    (fun i => Finset.sum_nonneg (fun j _ => hω j)) hcover
  have hωE := overlap_energy R ω kr kc hRrow hRcol
  have hρE : (∑ i, (U i-L i)^2) ≤ (lr:ℝ)*lc*(∑ j, (ρ j)^2) := by
    apply le_trans _ (overlap_energy S ρ lr lc hSrow hScol)
    exact Finset.sum_le_sum (fun i _ => pow_le_pow_left₀ (sub_nonneg.mpr (hLU i)) (hlocal i) 2)
  have hmul := mul_le_mul hωE hρE
    (Finset.sum_nonneg (fun i _ => sq_nonneg (U i-L i))) (by positivity)
  calc
    _ ≤ ((kr:ℝ)*kc*(∑ j, (ω j)^2)) * ((lr:ℝ)*lc*(∑ j, (ρ j)^2)) := henergy.trans hmul
    _ = _ := by ring

end CannonAnnular

namespace CannonAnnular

theorem finite_charge_cover {α β : Type*} [Fintype α] [Fintype β]
    (A : Finset α) (B : Finset β) (R : α → Finset β) (w : β → ℝ)
    (hw : ∀ j, 0 ≤ w j)
    (hcharge : ∀ j ∈ B, ∃ i ∈ A, j ∈ R i) :
    (∑ j ∈ B, w j) ≤ ∑ i ∈ A, ∑ j ∈ R i, w j := by
  classical
  calc
    _ ≤ ∑ j ∈ B, ∑ i ∈ A, if j ∈ R i then w j else 0 := by
      apply Finset.sum_le_sum
      intro j hj
      obtain ⟨i, hi, hij⟩ := hcharge j hj
      have hh := Finset.single_le_sum (s := A) (f := fun i => if j ∈ R i then w j else 0)
        (fun i _ => by split_ifs; exact hw j; exact le_rfl) hi
      simpa only [ite_eq_left hij] using hh
    _ = ∑ i ∈ A, ∑ j ∈ B, if j ∈ R i then w j else 0 := Finset.sum_comm
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i _
      rw [← Finset.sum_filter]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro j hj
        exact (Finset.mem_filter.mp hj).2
      · exact fun j _ _ => hw j

theorem interval_cover_of_charging {α β : Type*} [Fintype α] [Fintype β]
    (R : α → Finset β) (w : β → ℝ) (L U : α → ℝ)
    (hw : ∀ j, 0 ≤ w j) (t : ℝ) (B : Finset β)
    (hB : 1 ≤ ∑ j ∈ B, w j)
    (hcharge : ∀ j ∈ B, ∃ i, t ∈ Icc (L i) (U i) ∧ j ∈ R i) :
    1 ≤ ∑ i, (Icc (L i) (U i)).indicator (fun _ : ℝ => ∑ j ∈ R i, w j) t := by
  classical
  let A := Finset.univ.filter (fun i => t ∈ Icc (L i) (U i))
  have hh := finite_charge_cover A B R w hw (by
    intro j hj
    obtain ⟨i, hit, hij⟩ := hcharge j hj
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hit⟩, hij⟩)
  apply hB.trans (hh.trans_eq _)
  simp only [A, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : t ∈ Icc (L i) (U i) <;> simp [hi]

end CannonAnnular

namespace CannonAnnular

theorem annular_net_charge {X Y α : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (q : α → X) (h : X → Y) (f : X → ℝ) (L U : α → ℝ)
    (x y z : X) (ξ : Y) (R r C t : ℝ)
    (hR : 0 < R) (hr : 0 ≤ r) (hrR : r ≤ R / 2) (hC : 0 ≤ C)
    (hy : R ≤ dist y x ∧ dist y x ≤ 2*R)
    (hnet : ∃ i, dist (q i) y ≤ r)
    (hzoom : ∀ u v, dist u x ≤ 3*R → dist v x ≤ 3*R →
      dist (h u) (h v) ≤ C / R * dist u v)
    (hξ : dist ξ (h y) ≤ 2 * (r / R))
    (hz : dist z y ≤ r / 4) (hf : f z = t)
    (hrange : ∀ i z, dist z (q i) ≤ 2*r → f z ∈ Icc (L i) (U i)) :
    ∃ i, R/2 ≤ dist (q i) x ∧ dist (q i) x ≤ 3*R ∧
      t ∈ Icc (L i) (U i) ∧ dist ξ (h (q i)) ≤ (C+2)*(r/R) := by
  obtain ⟨i, hi⟩ := hnet
  have hqu : dist (q i) x ≤ 3*R := (dist_triangle (q i) y x).trans (by linarith [hy.2])
  have hql : R/2 ≤ dist (q i) x := by
    have hh := dist_triangle y (q i) x
    rw [dist_comm y (q i)] at hh
    linarith [hy.1]
  refine ⟨i, hql, hqu, ?_, ?_⟩
  · rw [← hf]
    apply hrange
    have hh := dist_triangle z y (q i)
    rw [dist_comm y (q i)] at hh
    linarith
  · have hqy : dist (h (q i)) (h y) ≤ C/R*r := by
      exact (hzoom _ _ hqu (by linarith [hy.2])).trans
        (mul_le_mul_of_nonneg_left hi (div_nonneg hC hR.le))
    have hh := dist_triangle ξ (h y) (h (q i))
    rw [dist_comm (h y) (h (q i))] at hh
    calc
      _ ≤ 2*(r/R) + C/R*r := hh.trans (add_le_add hξ hqy)
      _ = _ := by ring

theorem charged_center_in_annulus {X : Type*} [PseudoMetricSpace X]
    (x q p : X) (R d : ℝ) (hR : 0 ≤ R)
    (hq : R/2 ≤ dist q x ∧ dist q x ≤ 3*R)
    (hpq : dist p q ≤ d) (hd : d ≤ R/4) :
    R/4 ≤ dist p x ∧ dist p x ≤ 4*R := by
  constructor
  · have hh := dist_triangle q p x
    rw [dist_comm q p] at hh
    linarith [hq.1]
  · have hh := dist_triangle p q x
    linarith [hq.2]

end CannonAnnular

end

namespace CannonCapacity

open Finset Set

attribute [local instance] Classical.propDecidable

theorem bin_interval_detection {ι β : Type*} [Fintype ι] [Fintype β]
    (near : β → ι → Prop) (L U v t : ι → ℝ) (a b B : ℝ)
    (hab : a < b) (hLU : ∀ i, L i ≤ U i) (hv : ∀ i, 0 ≤ v i)
    (hlen : ∀ i, U i-L i = (b-a)*t i)
    (hmult : ∀ i, ((univ.filter (fun z : β => near z i)).card : ℝ) ≤ B)
    (hcover : ∀ z s, s ∈ Ioo a b →
      1 ≤ ∑ i, (Icc (L i) (U i)).indicator (fun _ : ℝ => if near z i then v i else 0) s) :
    (Fintype.card β : ℝ) ≤ B * ∑ i, v i*t i := by
  classical
  have ht : ∀ i, 0 ≤ t i := by
    intro i
    have := sub_nonneg.mpr (hLU i)
    rw [hlen] at this
    exact nonneg_of_mul_nonneg_right this (sub_pos.mpr hab)
  have hb (z : β) := CannonAnnular.weighted_open_interval_cover L U
    (fun i => if near z i then v i else 0) a b 1 hab.le hLU
    (fun i => by split_ifs; exact hv i; exact le_rfl) (hcover z)
  have hh := Finset.sum_le_sum (s := univ) (fun z _ => hb z)
  simp only [one_mul, sum_const, card_univ, nsmul_eq_mul] at hh
  have hr : ∑ z : β, ∑ i : ι, (if near z i then v i else 0)*(U i-L i) ≤
      (b-a)*(B * ∑ i, v i*t i) := by
    rw [sum_comm]
    calc
      _ = ∑ i : ι, ((univ.filter (fun z : β => near z i)).card : ℝ)*v i*((b-a)*t i) := by
        apply sum_congr rfl
        intro i _
        rw [← sum_mul,hlen,← sum_filter]
        simp
      _ ≤ ∑ i : ι, B*v i*((b-a)*t i) := by
        apply sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hmult i) (hv i)) (mul_nonneg (sub_pos.mpr hab).le (ht i))
      _ = _ := by simp_rw [show ∀ i, B*v i*((b-a)*t i) = (b-a)*B*(v i*t i) by intro i; ring]
                  rw [← mul_sum]; ring
  have hfinal := hh.trans hr
  rw [mul_comm (Fintype.card β : ℝ)] at hfinal
  exact (mul_le_mul_iff_right₀ (sub_pos.mpr hab)).mp hfinal

theorem mixed_capacity_of_detection {ι : Type*} [Fintype ι]
    (t σ : ι → ℝ) (ht : ∀ i, 0 ≤ t i) (hσ : ∀ i, 0 ≤ σ i)
    {L Q C B E bins : ℝ} (hL : 0 < L) (hQ : 0 < Q) (_hC : 0 ≤ C)
    (hB : 0 < B) (hE : 0 ≤ E) (hb : 0 ≤ bins)
    (henergy : ∑ i, (σ i)^2 ≤ E)
    (hlarge : 2*B*C ≤ L*bins)
    (hsmall : 4*B^2*E*C < Q*bins^2)
    (hdetect : bins ≤ B * ∑ i, (if L ≤ Q*t i then 1 else σ i)*t i) :
    C ≤ ∑ i, min (L*t i) (Q*(t i)^2) := by
  classical
  let large := univ.filter (fun i => L ≤ Q*t i)
  let small := univ.filter (fun i => ¬ L ≤ Q*t i)
  have hnon : ∀ i, 0 ≤ min (L*t i) (Q*(t i)^2) :=
    fun i => le_min (mul_nonneg hL.le (ht i)) (mul_nonneg hQ.le (sq_nonneg _))
  by_contra hn
  have hcap : ∑ i, min (L*t i) (Q*(t i)^2) < C := lt_of_not_ge hn
  have hla : L * (∑ i ∈ large, t i) ≤ C := by
    calc
      _ = ∑ i ∈ large, min (L*t i) (Q*(t i)^2) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro i hi
        have hh := (mem_filter.mp hi).2
        rw [min_eq_left (by nlinarith [mul_le_mul_of_nonneg_right hh (ht i)])]
      _ ≤ ∑ i, min (L*t i) (Q*(t i)^2) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun i _ _ => hnon i)
      _ ≤ C := hcap.le
  have hsm : Q * (∑ i ∈ small, (t i)^2) ≤ C := by
    calc
      _ = ∑ i ∈ small, min (L*t i) (Q*(t i)^2) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro i hi
        have hh := le_of_not_ge (mem_filter.mp hi).2
        rw [min_eq_right (by nlinarith [mul_le_mul_of_nonneg_right hh (ht i)])]
      _ ≤ ∑ i, min (L*t i) (Q*(t i)^2) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun i _ _ => hnon i)
      _ ≤ C := hcap.le
  have hde : bins ≤ B*((∑ i ∈ large, t i) + ∑ i ∈ small, σ i*t i) := by
    convert hdetect using 1
    congr 1
    simp only [large,small,sum_filter,← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    split_ifs <;> simp_all
  have hmass : bins ≤ 2*B*(∑ i ∈ small, σ i*t i) := by
    nlinarith
  have hCS := sum_mul_sq_le_sq_mul_sq small σ t
  have hsumσ : ∑ i ∈ small, (σ i)^2 ≤ E :=
    (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun i _ _ => sq_nonneg _)).trans henergy
  have hsmt : 0 ≤ ∑ i ∈ small, (t i)^2 := sum_nonneg (fun _ _ => sq_nonneg _)
  have hsms : 0 ≤ ∑ i ∈ small, σ i*t i := sum_nonneg (fun i _ => mul_nonneg (hσ i) (ht i))
  have hsquare : bins^2 ≤ 4*B^2*(∑ i ∈ small, σ i*t i)^2 := by
    nlinarith [sq_le_sq₀ hb (mul_nonneg (by positivity) hsms) |>.mpr hmass]
  have hcs' : (∑ i ∈ small, σ i*t i)^2 ≤ E*(∑ i ∈ small, (t i)^2) :=
    hCS.trans (mul_le_mul_of_nonneg_right hsumσ hsmt)
  have hbound : Q*bins^2 ≤ 4*B^2*E*C := by
    calc
      _ ≤ Q*(4*B^2*(∑ i ∈ small, σ i*t i)^2) := mul_le_mul_of_nonneg_left hsquare hQ.le
      _ ≤ Q*(4*B^2*(E*(∑ i ∈ small, (t i)^2))) := by gcongr
      _ = (4*B^2*E)*(Q*(∑ i ∈ small, (t i)^2)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hsm (by positivity)
  exact (not_lt_of_ge hbound) hsmall

end CannonCapacity

end

section

open Finset

namespace CannonCapacity

attribute [local instance] Classical.propDecidable

theorem weighted_separated_subset {ι : Type*} (S : Finset ι) (rel : ι → ι → Prop)
    (hself : ∀ i, rel i i) (hsymm : ∀ i j, rel i j → rel j i)
    (w : ι → ℝ) (hw : ∀ i ∈ S, 0 ≤ w i) (N : ℕ)
    (hN : ∀ i ∈ S, (S.filter (rel i)).card ≤ N) :
    ∃ T ⊆ S, (∀ i ∈ T, ∀ j ∈ T, i ≠ j → ¬ rel i j) ∧
      (∑ i ∈ S, w i) ≤ (N : ℝ) * ∑ i ∈ T, w i := by
  classical
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    by_cases hS : S.Nonempty
    · obtain ⟨i,hi,hmax⟩ := S.exists_max_image w hS
      let U := S.filter (fun j => ¬ rel i j)
      have hUS : U ⊆ S := filter_subset _ _
      have hiU : i ∉ U := by simp [U,hself]
      have hss : U ⊂ S := by
        refine ⟨hUS,?_⟩
        intro hh
        exact hiU (hh hi)
      obtain ⟨T,hTU,hsep,hbound⟩ := ih U hss
        (fun j hj => hw j (hUS hj)) (by
          intro j hj
          exact (Finset.card_le_card (Finset.filter_subset_filter _ hUS)).trans (hN j (hUS hj)))
      have hiT : i ∉ T := fun h => hiU (hTU h)
      refine ⟨insert i T,Finset.insert_subset_iff.mpr ⟨hi,hTU.trans hUS⟩,?_,?_⟩
      · intro j hj k hk hjk
        rcases mem_insert.mp hj with rfl | hjT
        · rcases mem_insert.mp hk with rfl | hk
          · exact fun _ => hjk rfl
          · exact (mem_filter.mp (hTU hk)).2
        · rcases mem_insert.mp hk with rfl | hk
          · exact fun h => (mem_filter.mp (hTU hjT)).2 (hsymm _ _ h)
          · exact hsep j hjT k hk hjk
      · have hnear : ∑ j ∈ S.filter (rel i), w j ≤ (N : ℝ)*w i := by
          calc
            _ ≤ ∑ j ∈ S.filter (rel i), w i := by
              exact Finset.sum_le_sum (fun j hj => hmax j (mem_filter.mp hj).1)
            _ = ((S.filter (rel i)).card : ℝ)*w i := by simp
            _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hN i hi) (hw i hi)
        have hsplit : (∑ j ∈ S, w j) =
            (∑ j ∈ S.filter (rel i), w j) + ∑ j ∈ U, w j := by
          symm
          exact Finset.sum_filter_add_sum_filter_not S (rel i) w
        rw [hsplit,Finset.sum_insert hiT]
        nlinarith
    · refine ⟨∅,empty_subset _,by simp,?_⟩
      simp [Finset.not_nonempty_iff_eq_empty.mp hS]

end CannonCapacity

end

namespace CannonCapacity

open Set Metric Finset

attribute [local instance] Classical.propDecidable

def clip (a b x : ℝ) : ℝ := max a (min b x)

lemma clip_mono (a b : ℝ) : Monotone (clip a b) := by
  intro x y hxy
  exact max_le_max le_rfl (min_le_min le_rfl hxy)

lemma mem_clipped_iff {a b l u t : ℝ} (ht : t ∈ Ioo a b) :
    t ∈ Icc (clip a b l) (clip a b u) ↔ t ∈ Icc l u := by
  simp only [Set.mem_Icc,clip]
  constructor
  · rintro ⟨hl,hu⟩
    constructor
    · by_contra hh
      have hh' : t < l := lt_of_not_ge hh
      have : t < min b l := lt_min ht.2 hh'
      exact (not_lt_of_ge ((le_max_right _ _).trans hl)) this
    · by_contra hh
      have hh' : u < t := lt_of_not_ge hh
      have : max a (min b u) < t := max_lt ht.1 (lt_of_le_of_lt (min_le_right _ _) hh')
      exact (not_lt_of_ge hu) this
  · rintro ⟨hl,hu⟩
    exact ⟨max_le ht.1.le ((min_le_right _ _).trans hl),
      (le_min ht.2.le hu).trans (le_max_right _ _)⟩

lemma clip_difference {a b l u : ℝ} (hab : a ≤ b) (hlu : l ≤ u) :
    clip a b u-clip a b l = max 0 (min b u-max a l) := by
  unfold clip
  rcases le_total l a with hla | hal
  · rw [min_eq_right (hla.trans hab),max_eq_left hla]
    rw [← max_sub_sub_right]
    simp only [sub_self,max_comm]
  · by_cases hlb : l ≤ b
    · rw [min_eq_right hlb,max_eq_right hal]
      have hmin : l ≤ min b u := le_min hlb hlu
      rw [max_eq_right (hal.trans hmin),max_eq_right (sub_nonneg.mpr hmin)]
    · have hbl := le_of_not_ge hlb
      simp only [min_eq_left (hbl.trans hlu),min_eq_left hbl,max_eq_right hab,sub_self,
        max_eq_right hal]
      exact (max_eq_left (by linarith)).symm

theorem clipped_bin_detection {ι β : Type*} [Fintype ι] [Fintype β]
    (lo hi t σ : ι → ℝ) (large : ι → Prop) (near : β → ι → Prop)
    (a b B : ℝ) (hab : a < b) (hlohi : ∀ i, lo i ≤ hi i)
    (hlen : ∀ i, clip a b (hi i)-clip a b (lo i) = (b-a)*t i)
    (hσ : ∀ i, 0 ≤ σ i)
    (hmult : ∀ i, ((univ.filter (fun z => near z i)).card : ℝ) ≤ B)
    (hunmarked : ∀ z s, s ∈ Ioo a b →
      (∀ i, large i → near z i → s ∈ Icc (lo i) (hi i) → False) →
      1 ≤ ∑ i, (Icc (lo i) (hi i)).indicator
        (fun _ : ℝ => if near z i ∧ ¬large i then σ i else 0) s) :
    (Fintype.card β : ℝ) ≤ B * ∑ i, (if large i then 1 else σ i)*t i := by
  apply bin_interval_detection near (fun i => clip a b (lo i))
    (fun i => clip a b (hi i)) (fun i => if large i then 1 else σ i) t
    a b B hab (fun i => clip_mono a b (hlohi i))
    (fun i => by split_ifs; norm_num; exact hσ i) hlen hmult
  intro z s hs
  by_cases hm : ∃ i, large i ∧ near z i ∧ s ∈ Icc (lo i) (hi i)
  · obtain ⟨i,hiL,hiN,hit⟩ := hm
    calc
      1 = (Icc (clip a b (lo i)) (clip a b (hi i))).indicator
          (fun _ : ℝ => if near z i then if large i then 1 else σ i else 0) s := by
        rw [indicator_of_mem ((mem_clipped_iff hs).mpr hit),ite_eq_left hiN,ite_eq_left hiL]
      _ ≤ ∑ j, (Icc (clip a b (lo j)) (clip a b (hi j))).indicator
          (fun _ : ℝ => if near z j then if large j then 1 else σ j else 0) s := by
        apply single_le_sum _ (mem_univ i)
        intro j _
        apply Set.indicator_nonneg
        intro _ _
        split_ifs; norm_num; exact hσ j; exact le_rfl
  · apply (hunmarked z s hs (by simpa only [not_exists,not_and] using hm)).trans
    apply sum_le_sum
    intro i _
    by_cases hit : s ∈ Icc (lo i) (hi i)
    · rw [indicator_of_mem hit,indicator_of_mem ((mem_clipped_iff hs).mpr hit)]
      by_cases hn : near z i <;> by_cases hl : large i <;> simp [hn,hl]
    · rw [indicator_of_notMem hit,indicator_of_notMem (fun hh => hit ((mem_clipped_iff hs).mp hh))]

theorem separated_capacity_of_detection {X : Type*} [MetricSpace X]
    {ι β : Type*} [Fintype ι] [Fintype β]
    (q : ι → X) (lo hi t σ : ι → ℝ) (near : β → ι → Prop)
    (a b B L Q E H r : ℝ) (N : ℕ) (hab : a < b)
    (hlohi : ∀ i, lo i ≤ hi i) (ht : ∀ i, 0 ≤ t i)
    (hlen : ∀ i, clip a b (hi i)-clip a b (lo i) = (b-a)*t i)
    (hσ : ∀ i, 0 ≤ σ i) (hL : 0 < L) (hQ : 0 < Q) (hB : 0 < B) (hE : 0 ≤ E)
    (hHr : 0 ≤ H*r) (hN : 0 < N)
    (hdegree : ∀ i, (univ.filter (fun j => dist (q i) (q j) ≤ H*r)).card ≤ N)
    (hmult : ∀ i, ((univ.filter (fun z => near z i)).card : ℝ) ≤ B)
    (henergy : ∑ i, (σ i)^2 ≤ E)
    (hlarge : 2*B*N ≤ L*Fintype.card β)
    (hsmall : 4*B^2*E*N < Q*(Fintype.card β : ℝ)^2)
    (hunmarked : ∀ z s, s ∈ Ioo a b →
      (∀ i, L ≤ Q*t i → near z i → s ∈ Icc (lo i) (hi i) → False) →
      1 ≤ ∑ i, (Icc (lo i) (hi i)).indicator
        (fun _ : ℝ => if near z i ∧ ¬L ≤ Q*t i then σ i else 0) s) :
    ∃ S : Finset ι, (∀ i ∈ S, ∀ j ∈ S, i ≠ j → H*r < dist (q i) (q j)) ∧
      1 ≤ ∑ i ∈ S, min (L*t i) (Q*(t i)^2) := by
  have hdetect := clipped_bin_detection lo hi t σ (fun i => L ≤ Q*t i) near a b B
    hab hlohi hlen hσ hmult hunmarked
  have hcap := mixed_capacity_of_detection t σ ht hσ hL hQ (by positivity : (0:ℝ) ≤ N)
    hB hE (by positivity) henergy hlarge hsmall hdetect
  obtain ⟨S,hS,hsep,hbound⟩ := weighted_separated_subset univ
    (fun i j => dist (q i) (q j) ≤ H*r) (by simpa using fun _i : ι => hHr)
    (fun i j h => by simpa only [dist_comm] using h)
    (fun i => min (L*t i) (Q*(t i)^2))
    (fun i _ => le_min (mul_nonneg hL.le (ht i)) (mul_nonneg hQ.le (sq_nonneg _))) N
    (fun i _ => hdegree i)
  refine ⟨S,fun i hi j hj hij => lt_of_not_ge (hsep i hi j hj hij),?_⟩
  have hN' : (0:ℝ) < N := by exact_mod_cast hN
  nlinarith [hcap.trans hbound]

end CannonCapacity

end

section

section

open Set MeasureTheory
open scoped BigOperators
open Set unitInterval

namespace CannonAnnular

theorem radial_subinterval (g : I → ℝ) (hg : Continuous g)
    (r s : ℝ) (hrs : r < s) (hzero : g 0 ≤ r) (hone : s ≤ g 1) :
    ∃ a b : I, a < b ∧ g a = r ∧ g b = s ∧
      ∀ t ∈ Icc a b, g t ∈ Icc r s := by
  have hnon : (g ⁻¹' {s}).Nonempty := by
    obtain ⟨t, _, ht⟩ := intermediate_value_Icc (show (0:I) ≤ 1 from zero_le)
      hg.continuousOn ⟨hzero.trans hrs.le, hone⟩
    exact ⟨t, ht⟩
  have hc : IsCompact (g ⁻¹' {s}) := (isClosed_singleton.preimage hg).isCompact
  obtain ⟨b, hb, hbmin⟩ := hc.exists_isMinOn hnon continuous_id.continuousOn
  have hgb : g b = s := hb
  have hnonr : (Icc (0:I) b ∩ g ⁻¹' {r}).Nonempty := by
    obtain ⟨t, ht, htr⟩ := intermediate_value_Icc (show (0:I) ≤ b from zero_le) hg.continuousOn
      ⟨hzero, hgb ▸ hrs.le⟩
    exact ⟨t, ht, htr⟩
  have hcr : IsCompact (Icc (0:I) b ∩ g ⁻¹' {r}) :=
    isCompact_Icc.inter_right (isClosed_singleton.preimage hg)
  obtain ⟨a, ha, hamax⟩ := hcr.exists_isMaxOn hnonr continuous_id.continuousOn
  have hga : g a = r := ha.2
  have hab : a < b := lt_of_le_of_ne ha.1.2 (by intro he; rw [he, hgb] at hga; exact hrs.ne hga.symm)
  refine ⟨a, b, hab, hga, hgb, ?_⟩
  intro t ht
  constructor
  · by_contra hn
    have hlt : g t < r := lt_of_not_ge hn
    obtain ⟨z, hz, hzr⟩ := intermediate_value_Icc ht.2 hg.continuousOn
      ⟨hlt.le, hgb ▸ hrs.le⟩
    have hza : z ≤ a := hamax ⟨⟨zero_le, hz.2⟩, hzr⟩
    have htz : t < z := lt_of_le_of_ne hz.1 (by intro he; rw [← he] at hzr; exact hlt.ne hzr)
    exact (not_lt_of_ge (hza.trans ht.1)) htz
  · by_contra hn
    have hlt : s < g t := lt_of_not_ge hn
    obtain ⟨z, hz, hzs⟩ := intermediate_value_Icc (show (0:I) ≤ t from zero_le) hg.continuousOn
      ⟨hzero.trans hrs.le, hlt.le⟩
    have hbz : b ≤ z := hbmin hzs
    have hzt : z < t := lt_of_le_of_ne hz.2 (by intro he; rw [he] at hzs; exact hlt.ne' hzs)
    exact (not_lt_of_ge (ht.2.trans hbz)) hzt

end CannonAnnular

namespace CannonAnnular

theorem radial_subpath {X : Type*} [PseudoMetricSpace X] (o x y : X)
    (p : Path x y) (r s : ℝ) (hrs : r < s)
    (hx : dist x o ≤ r) (hy : s ≤ dist y o) :
    ∃ u v : X, ∃ q : Path u v,
      Set.range q ⊆ Set.range p ∧ dist u o = r ∧ dist v o = s ∧
      s-r ≤ dist u v ∧ ∀ t, dist (q t) o ∈ Icc r s := by
  obtain ⟨a, b, hab, ha, hb, hbetween⟩ := radial_subinterval
    (fun t => dist (p t) o) (p.continuous.dist continuous_const) r s hrs
    (by simpa using hx) (by simpa using hy)
  refine ⟨p a, p b, p.subpath a b, ?_, ha, hb, ?_, ?_⟩
  · rw [Path.range_subpath_of_le _ _ _ hab.le]
    exact Set.image_subset_range _ _
  · have hh := dist_triangle (p b) (p a) o
    rw [dist_comm (p b) (p a), ha, hb] at hh
    linarith
  · intro t
    have ht : (p.subpath a b) t ∈ Set.range (p.subpath a b) := Set.mem_range_self _
    rw [Path.range_subpath_of_le _ _ _ hab.le] at ht
    obtain ⟨z, hz, hzt⟩ := ht
    rw [← hzt]
    exact hbetween z hz

theorem continuum_neighborhood_path {X : Type*} [TopologicalSpace X]
    [LocallyPathConnectedSpace X] {K V : Set X} (hK : IsPreconnected K)
    (hV : IsOpen V) (hKV : K ⊆ V) {x y : X} (hx : x ∈ K) (hy : y ∈ K) :
    JoinedIn V x y := by
  let : PreconnectedSpace K := Subtype.preconnectedSpace hK
  let : LocallyPathConnectedSpace V := hV.locallyPathConnectedSpace
  let f : K → V := fun z => ⟨z.val, hKV z.property⟩
  have hf : Continuous f := continuous_subtype_val.subtype_mk _
  have hconn : IsPreconnected (Set.range f) := isPreconnected_range hf
  have hmem : f ⟨y,hy⟩ ∈ connectedComponent (f ⟨x,hx⟩) :=
    hconn.subset_connectedComponent ⟨⟨x,hx⟩, rfl⟩ ⟨⟨y,hy⟩, rfl⟩
  rw [← pathComponent_eq_connectedComponent] at hmem
  obtain ⟨p⟩ := hmem
  exact ⟨p.map continuous_subtype_val, fun t => (p t).property⟩

theorem annular_path_near_continuum {X : Type*} [PseudoMetricSpace X]
    [LocallyPathConnectedSpace X] (o : X) (r s : ℝ) (hrs : r < s)
    (K V : Set X) (hK : IsPreconnected K) (hV : IsOpen V) (hKV : K ⊆ V)
    {x y : X} (hx : x ∈ K) (hy : y ∈ K)
    (hxr : dist x o ≤ r) (hys : s ≤ dist y o) :
    ∃ u v : X, ∃ q : Path u v,
      Set.range q ⊆ V ∧ dist u o = r ∧ dist v o = s ∧
      s-r ≤ dist u v ∧ ∀ t, dist (q t) o ∈ Icc r s := by
  obtain ⟨p, hp⟩ := continuum_neighborhood_path hK hV hKV hx hy
  obtain ⟨u, v, q, hqp, hu, hv, huv, hq⟩ := radial_subpath o x y p r s hrs hxr hys
  refine ⟨u, v, q, ?_, hu, hv, huv, hq⟩
  rintro z hz
  obtain ⟨t, rfl⟩ := hqp hz
  exact hp t

end CannonAnnular

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
