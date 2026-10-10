import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.Core

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter
open ArithmeticFunction
open MeasureTheory Finset
open Classical
open Classical Finset
open Classical Finset Real MeasureTheory
open scoped ContDiff

namespace OrdinaryAnalyticCentering
open Finset OrdinaryCorrelations OrdinaryTwistWidth OrdinaryAnalyticCutoff

lemma shifted_multiples_card (N a p : ℕ) :
    ((Finset.Icc 1 N).filter (fun n=>p∣n+a)).card≤(N+a)/p := by
  have h := card_le_card_of_injOn (fun n=>n+a)
    (s:=(Finset.Icc 1 N).filter (fun n=>p∣n+a))
    (t:=(Finset.Icc 1 (N+a)).filter (fun n=>p∣n)) (by
      intro n hn
      obtain ⟨hn,hp⟩:=mem_filter.mp hn
      obtain ⟨hn1,hnN⟩:=Finset.mem_Icc.mp hn
      exact mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by dsimp;omega,by dsimp;omega⟩,hp⟩)
    (by intro n hn m hm he;dsimp at he;omega)
  exact h.trans_eq (SourcePrimeFactor.multiples_Icc_card (N+a) p)

noncomputable def badSet (u a N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (fun n=>¬(u.Coprime n ∧ u.Coprime (n+a)))

lemma badSet_card (u a N J : ℕ) (hu : 0<u) (huJ : u.primeFactors.card≤J)
    (P : ℝ) (hP : 0<P) (huP : ∀p∈u.primeFactors,P≤p) (haN : a≤N) :
    ((badSet u a N).card:ℝ)≤3*(J:ℝ)*(N:ℝ)/P := by
  classical
  let F (p:ℕ) := ((Finset.Icc 1 N).filter (fun n=>p∣n))∪
    ((Finset.Icc 1 N).filter (fun n=>p∣n+a))
  have hsub : badSet u a N⊆u.primeFactors.biUnion F := by
    intro n hn
    obtain ⟨hnI,hn⟩:=mem_filter.mp hn
    rcases not_and_or.mp hn with hn|hn
    · obtain ⟨p,hp,hpu,hpn⟩:=Nat.Prime.not_coprime_iff_dvd.mp hn
      exact mem_biUnion.mpr ⟨p,Nat.mem_primeFactors.mpr ⟨hp,hpu,hu.ne'⟩,
        mem_union_left _ (mem_filter.mpr ⟨hnI,hpn⟩)⟩
    · obtain ⟨p,hp,hpu,hpn⟩:=Nat.Prime.not_coprime_iff_dvd.mp hn
      exact mem_biUnion.mpr ⟨p,Nat.mem_primeFactors.mpr ⟨hp,hpu,hu.ne'⟩,
        mem_union_right _ (mem_filter.mpr ⟨hnI,hpn⟩)⟩
  have hc : (badSet u a N).card≤∑p∈u.primeFactors,(F p).card :=
    (Finset.card_le_card hsub).trans card_biUnion_le
  have hF (p:ℕ) (hp:p∈u.primeFactors) : ((F p).card:ℝ)≤3*(N:ℝ)/P := by
    have hp0 : 0<(p:ℝ) := lt_of_lt_of_le hP (huP p hp)
    have hs := (Finset.card_union_le _ _).trans (_root_.add_le_add
      (le_of_eq (SourcePrimeFactor.multiples_Icc_card N p)) (shifted_multiples_card N a p))
    have hs' : ((F p).card:ℝ)≤((N/p:ℕ):ℝ)+(((N+a)/p:ℕ):ℝ) := by exact_mod_cast hs
    have h1 : ((N/p:ℕ):ℝ)≤(N:ℝ)/(p:ℝ) := Nat.cast_div_le
    have h2 : (((N+a)/p:ℕ):ℝ)≤((N+a:ℕ):ℝ)/(p:ℝ) := Nat.cast_div_le
    have haN' : (a:ℝ)≤N := by exact_mod_cast haN
    have h3 : (N:ℝ)/p+((N+a:ℕ):ℝ)/p≤3*(N:ℝ)/p := by
      rw [← add_div,Nat.cast_add]
      gcongr
      linarith
    exact (hs'.trans (_root_.add_le_add h1 h2)).trans
      (h3.trans (div_le_div_of_nonneg_left (by positivity) hP (huP p hp)))
  have hc' : ((badSet u a N).card:ℝ)≤∑p∈u.primeFactors,((F p).card:ℝ) := by exact_mod_cast hc
  apply hc'.trans
  calc
    _ ≤∑p∈u.primeFactors,3*(N:ℝ)/P := sum_le_sum hF
    _ = (u.primeFactors.card:ℝ)*(3*(N:ℝ)/P) := by simp
    _ ≤(J:ℝ)*(3*(N:ℝ)/P) := by gcongr
    _ = _ := by ring

lemma norm_cutoff_le_one (phi : ℝ→ℝ) (hφ : ∀x,0≤phi x ∧ phi x≤1)
    (P : Finset ℕ) (mu : ℝ) (n : ℕ) : ‖cutoff phi P mu n‖≤1 := by
  rw [cutoff,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hφ _).1]
  exact (hφ _).2

lemma cutoff_mul (phi : ℝ→ℝ) (P : Finset ℕ) (hP : ∀p∈P,p.Prime)
    (mu : ℝ) (u n : ℕ) (hu : ∀p∈P,¬p∣u) :
    cutoff phi P mu (u*n)=cutoff phi P mu n := by
  have he : primeCount P (u*n)=primeCount P n := by
    unfold primeCount
    congr 1
    ext p
    by_cases hp:p∈P
    · simp only [mem_filter,hp,true_and,(hP p hp).dvd_mul,hu p hp,false_or]
    · simp [hp]
  simp only [cutoff,he]

lemma multiplicative_product_error (f g : ℕ→ℂ) (hf : OneBounded f) (hg : OneBounded g)
    (hfm : Multiplicative f) (hgm : Multiplicative g)
    (u a N : ℕ) (hu : 0<u) (v : ℕ) (hv : v∈Finset.Icc 1 N) :
    ‖f (u*v)*g (u*(v+a))-(f u*g u)*(f v*g (v+a))‖≤
      if v∈badSet u a N then (2:ℝ) else 0 := by
  by_cases hc : u.Coprime v ∧ u.Coprime (v+a)
  · have hv0 : 0<v := (Finset.mem_Icc.mp hv).1
    rw [hfm u v hu hv0 hc.1,hgm u (v+a) hu (by omega) hc.2]
    have he : (f u*f v)*(g u*g (v+a))-(f u*g u)*(f v*g (v+a))=0 := by ring
    rw [he,norm_zero]
    positivity
  · have hvb : v∈badSet u a N := mem_filter.mpr ⟨hv,hc⟩
    rw [ite_eq_left hvb]
    apply (norm_sub_le _ _).trans
    have hf1 := mul_le_mul (hf (u*v)) (hg (u*(v+a))) (norm_nonneg _) (by positivity)
    have hf2 : ‖f u‖*‖g u‖≤1 := by nlinarith [mul_le_mul (hf u) (hg u) (norm_nonneg _) (by positivity)]
    have hf3 : ‖f v‖*‖g (v+a)‖≤1 := by nlinarith [mul_le_mul (hf v) (hg (v+a)) (norm_nonneg _) (by positivity)]
    rw [norm_mul,norm_mul,norm_mul,norm_mul]
    nlinarith [mul_le_mul hf2 hf3 (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by positivity)]
end OrdinaryAnalyticCentering

end

end OAI
