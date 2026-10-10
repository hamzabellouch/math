import Mathlib
import OAI.Combinatorics.SharpRamsey.Selection.UniversalTables

namespace OAI

section
namespace SharpLogRamsey.PublicTables
open Finset Real
open scoped Classical BigOperators
noncomputable section
variable {Ω ι X : Type*} [Fintype Ω] [Fintype ι] [Fintype X]

omit [Fintype X] in

theorem decoder_cover (p : Law Ω) (A : ι→Ω→Prop) (a H cap size : ℝ)
    (Q : ℕ) (decode : Ω→Fin (Q+1)→Finset X) (support : ι→Finset X)
    (ha : 0≤a) (hcard : (Fintype.card ι:ℝ)≤exp H) (hH : H+1≤exp a)
    (hp : ∀ i,exp (-a)≤acceptProb p (A i))
    (hgood : ∀ i z,A i z → ∃ h,cap≤((support i)∩decode z h).card ∧
      ((decode z h).card:ℝ)≤ size) :
    ∃ m : Finset (Ω×Fin (Q+1)),
      m.card≤⌈exp (2*a)⌉₊*(Q+1) ∧
      (∀ z∈m,((decode z.1 z.2).card:ℝ)≤ size) ∧
      (∀ i,∃ z∈m,cap≤((support i)∩decode z.1 z.2).card) ∧
      log ((m.card:ℝ)+1)≤2*a+log 3+log ((Q:ℝ)+1) := by
  obtain ⟨r,hr,hits,hlen⟩ := exists_cover p A a H ha hcard hH hp
  let m := (r×ˢ(univ:Finset (Fin (Q+1)))).filter (fun z => ((decode z.1 z.2).card:ℝ)≤ size)
  have hm : m.card≤⌈exp (2*a)⌉₊*(Q+1) := by
    apply (card_filter_le _ _).trans
    rw [card_product,card_univ,Fintype.card_fin]
    exact Nat.mul_le_mul_right _ hr
  refine ⟨m,hm,?_,?_,?_⟩
  · intro z hz
    exact (mem_filter.mp hz).2
  · intro i
    obtain ⟨z,hzr,hzi⟩ := hits i
    obtain ⟨h,hcap,hsize⟩ := hgood i z hzi
    exact ⟨(z,h),mem_filter.mpr ⟨mem_product.mpr ⟨hzr,mem_univ _⟩,hsize⟩,hcap⟩
  · have hh : (m.card:ℝ)+1≤((⌈exp (2*a)⌉₊:ℝ)+1)*((Q:ℝ)+1) := by
      have hh : (m.card:ℝ)≤(⌈exp (2*a)⌉₊:ℝ)*((Q:ℝ)+1) := by exact_mod_cast hm
      nlinarith [(show (0:ℝ)≤Q by positivity)]
    calc
      _ ≤ log (((⌈exp (2*a)⌉₊:ℝ)+1)*((Q:ℝ)+1)) := log_le_log (by positivity) hh
      _ = log ((⌈exp (2*a)⌉₊:ℝ)+1)+log ((Q:ℝ)+1) := log_mul (by positivity) (by positivity)
      _ ≤ _ := by linarith only [hlen]

omit [Fintype Ω] [Fintype ι] [Fintype X] in
lemma sampling_exponent {n u : ℝ} (hn : 0<n) (hu : 0<u) (M : ℕ) (e : ℝ) :
    (n/u)^M*(exp (-e)/4)=exp (-((M:ℝ)*log (u/n)+e+log 4)) := by
  have hh : exp ((M:ℝ)*log (u/n)+e+log 4)=(u/n)^M*exp e*4 := by
    rw [exp_add,exp_add,exp_nat_mul,exp_log (div_pos hu hn),exp_log (by norm_num : (0:ℝ)<4)]
  rw [exp_neg,exp_neg,hh]
  simp only [div_pow]
  field_simp

end
end SharpLogRamsey.PublicTables

end

end OAI
