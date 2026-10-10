import Mathlib
import OAI.Combinatorics.KMedian.Compression.GaussianCircuit
import OAI.Combinatorics.KMedian.Compression.DependentIntegerKernel

namespace OAI

namespace MetricKMedian.Gaussian
open Finset

theorem circuit_integer_ratio {r n : ℕ} (V : Fin r → Fin n → ℤ)
    (z : Fin n → ℚ) (L : ℕ) (hV : ∀ i j, |V i j| ≤ (2:ℤ)^L)
    (hz : ∀ i, ∑ j, (V i j:ℚ)*z j=0)
    (hc : IsCircuit (fun i j => (V i j:ℚ)) z) (w : Fin n) (hw : z w=1) :
    ∃ U : Fin n → ℤ, U w ≠ 0 ∧
      (∀ j, |U j| ≤ (2:ℤ)^(2*r*(r+L))) ∧
      ∀ j, z j=(U j:ℚ)/(U w:ℚ) := by
  classical
  let S := univ.filter (fun j => z j ≠ 0)
  have hwS : w ∈ S := by simp only [S,mem_filter,mem_univ,true_and,hw,ne_eq,one_ne_zero,not_false_eq_true]
  have hdep : ¬ LinearIndependent ℚ (fun j : ↥S => fun i => (V i j.val:ℚ)) := by
    intro hi
    have hsum : ∑ j : ↥S, z j.val • (fun i => (V i j.val:ℚ))=0 := by
      funext i
      simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply]
      rw [sum_coe_sort S (fun j => z j*(V i j:ℚ))]
      have he : (∑ j ∈ S, z j*(V i j:ℚ))=∑ j, z j*(V i j:ℚ) := by
        apply sum_subset (subset_univ _)
        intro j _ hj
        have he : z j=0 := by simpa only [S,mem_filter,mem_univ,true_and,not_not] using hj
        rw [he,zero_mul]
      rw [he]
      simpa only [mul_comm] using hz i
    have hh := (Fintype.linearIndependent_iff.mp hi) (fun j => z j.val) hsum ⟨w,hwS⟩
    rw [hw] at hh
    exact one_ne_zero hh
  obtain ⟨u,hune,hb,hker⟩ := Compression.full_integer_kernel_of_dependent
    (fun i (j : ↥S) => V i j.val) L (fun i j => hV i j.val) hdep
  let U : Fin n → ℤ := fun j => if h : j ∈ S then u ⟨j,h⟩ else 0
  have hUval : ∀ j : ↥S, U j.val=u j := by intro j; simp only [U,dite_eq_left j.property]
  have hUne : ∃ j, U j ≠ 0 := by
    obtain ⟨j,hj⟩ := hune
    exact ⟨j.val,by rwa [hUval]⟩
  have hUz : ∀ j, z j=0 → U j=0 := by
    intro j hj
    have hn : j ∉ S := by simp only [S,mem_filter,mem_univ,true_and,hj,ne_eq,not_true_eq_false,not_false_eq_true]
    exact dite_eq_right hn
  have hUker : ∀ i, ∑ j, (V i j:ℚ)*(U j:ℚ)=0 := by
    intro i
    have hh : (∑ j, U j*V i j)=∑ j : ↥S, u j*V i j.val := by
      calc
        _ = ∑ j ∈ S, U j*V i j := by
          symm
          apply sum_subset (subset_univ _)
          intro j _ hj
          simp only [U,dite_eq_right hj,zero_mul]
        _ = _ := by rw [← sum_coe_sort]; exact sum_congr rfl (fun j _ => by rw [hUval])
    have hh' := hh.trans (hker i)
    have hcast : (∑ j, (U j:ℚ)*(V i j:ℚ))=0 := by exact_mod_cast hh'
    simpa only [mul_comm] using hcast
  obtain ⟨t,ht⟩ := hc (fun j => (U j:ℚ)) (by intro j hj; exact_mod_cast hUz j hj) hUker
  have htw : (U w:ℚ)=t := by simpa only [hw,mul_one] using ht w
  have htn : t ≠ 0 := by
    intro ht0
    obtain ⟨j,hj⟩ := hUne
    have hh := ht j
    rw [ht0,zero_mul] at hh
    exact hj (by exact_mod_cast hh)
  have hUw : U w ≠ 0 := by intro hn; simp only [hn,Int.cast_zero] at htw; exact htn htw.symm
  refine ⟨U,hUw,?_,?_⟩
  · intro j
    by_cases hj : j ∈ S
    · rw [show U j=u ⟨j,hj⟩ from dite_eq_left hj]
      simpa only [Fintype.card_fin] using hb ⟨j,hj⟩
    · rw [show U j=0 from dite_eq_right hj,abs_zero]; positivity
  · intro j
    rw [htw]
    apply (eq_div_iff htn).mpr
    rw [ht j]
    ring

theorem ratio_num_den_bound (a b : ℤ) (hb : b ≠ 0) (H : ℤ)
    (ha : |a| ≤ H) (hbH : |b| ≤ H) :
    |((a:ℚ)/(b:ℚ)).num| ≤ H ∧ (((a:ℚ)/(b:ℚ)).den:ℤ) ≤ H := by
  let q := (a:ℚ)/(b:ℚ)
  obtain ⟨c,hcA,hcB⟩ := Rat.num_den_mk hb (q := q) (by exact (Rat.divInt_eq_div a b).symm)
  have hc : c ≠ 0 := by intro hz; rw [hz,zero_mul] at hcB; exact hb hcB
  have hc1 : (1:ℤ) ≤ |c| := by
    have ha := abs_pos.mpr hc
    omega
  have hnum : |q.num| ≤ |a| := by
    rw [hcA,abs_mul]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hc1 (abs_nonneg q.num)
  have hden : (q.den:ℤ) ≤ |b| := by
    rw [hcB,abs_mul,abs_of_nonneg (by positivity : (0:ℤ) ≤ q.den)]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hc1 (Int.natCast_nonneg q.den)
  exact ⟨hnum.trans ha,hden.trans hbH⟩

theorem integer_input_kernel_bounds (r n L : ℕ) (V : Fin r → Fin n → ℤ)
    (hn : r < n) (hV : ∀ i j, |V i j| ≤ (2:ℤ)^L) :
    let z := kernel r n (fun i j => (V i j:ℚ))
    ∀ j, |(z j).num| ≤ (2:ℤ)^(2*r*(r+L)) ∧
      ((z j).den:ℤ) ≤ (2:ℤ)^(2*r*(r+L)) := by
  dsimp only
  obtain ⟨⟨w,hw⟩,hc⟩ := kernel_circuit r n (fun i j => (V i j:ℚ)) hn
  have hk := (kernel_spec r n (fun i j => (V i j:ℚ)) hn).2
  obtain ⟨U,hUw,hU,hz⟩ := circuit_integer_ratio V _ L hV hk hc w hw
  intro j
  rw [hz j]
  exact ratio_num_den_bound (U j) (U w) hUw _ (hU j) (hU w)

end MetricKMedian.Gaussian

end OAI
