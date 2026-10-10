import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.MeanC
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.SmoothRoughCorrelation
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.ShiftedMultiplesCard

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
open Finset Filter OrdinaryCorrelations OrdinaryTwistWidth OrdinaryAnalyticCutoff
open scoped ContDiff

lemma reciprocal_range_mass (M τ : ℝ) (hM : 0<M) (hτ : τ<2) (Z : Finset ℕ)
    (hZ : ∀z∈Z,M<z ∧ (z:ℝ)≤τ*M) : ∑z∈Z,(z:ℝ)⁻¹≤2 := by
  classical
  by_cases he : Z.Nonempty
  swap
  · have hz : Z=∅ := not_nonempty_iff_eq_empty.mp he
    simp [hz]
  have hτM : 0≤τ*M := by
    obtain ⟨z,hz⟩:=he
    exact (lt_trans hM (hZ z hz).1).le.trans (hZ z hz).2
  have hsub : Z⊆Icc 1 ⌊τ*M⌋₊ := by
    intro z hz
    have hz0 : 0<(z:ℝ) := hM.trans (hZ z hz).1
    exact Finset.mem_Icc.mpr ⟨by exact_mod_cast (show (1:ℕ)≤z by exact_mod_cast hz0),
      (Nat.le_floor_iff hτM).mpr (hZ z hz).2⟩
  have hc : (Z.card:ℝ)≤τ*M := by
    have hn := Finset.card_le_card hsub
    rw [Nat.card_Icc] at hn
    have hc' : (Z.card:ℝ)≤⌊τ*M⌋₊ := by exact_mod_cast hn
    exact hc'.trans (Nat.floor_le hτM)
  calc
    _ ≤∑_z∈Z,M⁻¹ := sum_le_sum (fun z hz=>inv_anti₀ hM (hZ z hz).1.le)
    _ = (Z.card:ℝ)/M := by simp [div_eq_mul_inv]
    _ ≤τ := (div_le_iff₀ hM).mpr hc
    _ ≤2 := hτ.le

lemma sum_product_error (f g : ℕ→ℂ) (hf : OneBounded f) (hg : OneBounded g)
    (hfm : Multiplicative f) (hgm : Multiplicative g)
    (u a N J : ℕ) (hu : 0<u) (huJ : u.primeFactors.card≤J)
    (Q : ℝ) (hQ : 0<Q) (huQ : ∀p∈u.primeFactors,Q≤p) (haN : a≤N)
    (phi : ℝ→ℝ) (hφb : ∀x,0≤phi x ∧ phi x≤1) (P : Finset ℕ) (mu : ℝ) :
    ‖∑v∈Icc 1 N,(f (u*v)*g (u*(v+a))-(f u*g u)*(f v*g (v+a)))*
      cutoff phi P mu v*cutoff phi P mu (v+a)‖≤6*(J:ℝ)*(N:ℝ)/Q := by
  have hpoint (v:ℕ) (hv:v∈Finset.Icc 1 N) :
      ‖(f (u*v)*g (u*(v+a))-(f u*g u)*(f v*g (v+a)))*
        cutoff phi P mu v*cutoff phi P mu (v+a)‖≤(if v∈badSet u a N then (2:ℝ) else 0) := by
    rw [norm_mul,norm_mul]
    have h1 := norm_cutoff_le_one phi hφb P mu v
    have h2 := norm_cutoff_le_one phi hφb P mu (v+a)
    calc
      _ ≤ ‖f (u*v)*g (u*(v+a))-(f u*g u)*(f v*g (v+a))‖*1*1 := by gcongr
      _ = _ := by ring
      _ ≤_ := multiplicative_product_error f g hf hg hfm hgm u a N hu v hv
  have hsum : (∑v∈Icc 1 N,if v∈badSet u a N then (2:ℝ) else 0)=
      2*((badSet u a N).card:ℝ) := by
    rw [← sum_filter]
    have he : (Finset.Icc 1 N).filter (fun v=>v∈badSet u a N)=badSet u a N :=
      filter_mem_eq_inter.trans (inter_eq_right.mpr (filter_subset _ _))
    rw [he,sum_const,nsmul_eq_mul,mul_comm]
  have hnorm := (norm_sum_le _ _).trans (sum_le_sum hpoint)
  rw [hsum] at hnorm
  have hc := badSet_card u a N J hu huJ Q hQ huQ haN
  exact hnorm.trans ((mul_le_mul_of_nonneg_left hc (by norm_num : (0:ℝ)≤2)).trans_eq (by ring))

lemma dilation_rough_correlation (h : ℕ) (hh : 0<h) (phi : ℝ→ℝ)
    (hφ : ContDiff ℝ ∞ phi) (hφc : HasCompactSupport phi)
    (hφb : ∀x,0≤phi x ∧ phi x≤1) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ B : ℝ in atTop,
    ∀ τ : ℝ, 1<τ → τ<2 → ∀ M : ℝ, Real.exp (B^(9999/10000:ℝ))/τ≤M →
    ∀ Z : Finset ℕ,
    (∀z∈Z,M<z ∧ (z:ℝ)≤τ*M ∧ SourceRoughFourier.IsRough (P₀ B) z) →
    ∀ f g : ℕ→ℂ, OneBounded f → OneBounded g → Multiplicative f → Multiplicative g →
    (UniformlyNonpretentious f ∨ UniformlyNonpretentious g) →
    ∀ P : Finset ℕ, (∀p∈P,p.Prime) →
    ∀ c : ℕ→ℂ, (∀z∈Z,‖c z‖≤1) →
    ∀u J:ℕ,0<u →u.primeFactors.card≤J → (∀p∈u.primeFactors,P₀ B≤p) →
    ∀ᶠ Y : ℝ in atTop, ∀mu:ℝ,
      ‖∑v∈Icc 1 ⌊Y⌋₊,∑z∈Z,(c z/(z:ℂ))*f (u*v)*g (u*(v+h*z))*
        cutoff phi P mu v*cutoff phi P mu (v+h*z)‖≤
      (C*B^(-10001/10000:ℝ)+12*(J:ℝ)/P₀ B)*Y := by
  obtain ⟨C,hC,hMain⟩:=smooth_rough_correlation h hh phi hφ hφc hφb
  refine ⟨C,hC,?_⟩
  filter_upwards [hMain,eventually_ge_atTop (1:ℝ)] with B hB hB1
  intro τ hτ1 hτ2 M hM Z hZ f g hf hg hfm hgm hNP P hP c hc u J hu huJ huQ
  have hQ : 0<P₀ B := Real.exp_pos _
  have hM0 : 0<M := lt_of_lt_of_le (div_pos (Real.exp_pos _) (by linarith)) hM
  have hMass:=reciprocal_range_mass M τ hM0 hτ2 Z (fun z hz=>⟨(hZ z hz).1,(hZ z hz).2.1⟩)
  have he := hB τ hτ1 hτ2 M hM Z hZ f g hf hg hfm hgm hNP P hP c hc
  have hlarge : ∀ᶠ Y:ℝ in atTop,∀z∈Z,h*z≤⌊Y⌋₊ := by
    apply (eventually_all_finset Z).mpr
    intro z hz
    exact tendsto_nat_floor_atTop.eventually_ge_atTop (h*z)
  filter_upwards [he,hlarge,eventually_ge_atTop (0:ℝ)] with Y hY hlarge hY0
  intro mu
  let E (z:ℕ) : ℂ := ∑v∈Icc 1 ⌊Y⌋₊,
    (f (u*v)*g (u*(v+h*z))-(f u*g u)*(f v*g (v+h*z)))*
      cutoff phi P mu v*cutoff phi P mu (v+h*z)
  have hE (z:ℕ) (hz:z∈Z) : ‖E z‖≤6*(J:ℝ)*(⌊Y⌋₊:ℝ)/P₀ B :=
    sum_product_error f g hf hg hfm hgm u (h*z) ⌊Y⌋₊ J hu huJ (P₀ B)
      (Real.exp_pos _) huQ (hlarge z hz) phi hφb P mu
  have herror : ‖∑z∈Z,(c z/(z:ℂ))*E z‖≤12*(J:ℝ)/P₀ B*Y := by
    apply (norm_sum_le _ _).trans
    have hpoint (z:ℕ) (hz:z∈Z) : ‖c z/(z:ℂ)*E z‖≤
        (z:ℝ)⁻¹*(6*(J:ℝ)*(⌊Y⌋₊:ℝ)/P₀ B) := by
      rw [norm_mul,norm_div,Complex.norm_natCast]
      apply mul_le_mul _ (hE z hz) (norm_nonneg _) (by positivity)
      simpa only [one_div] using div_le_div_of_nonneg_right (hc z hz) (Nat.cast_nonneg z)
    apply (sum_le_sum hpoint).trans
    rw [← sum_mul]
    calc
      _ ≤2*(6*(J:ℝ)*(⌊Y⌋₊:ℝ)/P₀ B) := by gcongr
      _ ≤2*(6*(J:ℝ)*Y/P₀ B) := by gcongr;exact Nat.floor_le hY0
      _ = _ := by ring
  have heq : (∑v∈Icc 1 ⌊Y⌋₊,∑z∈Z,(c z/(z:ℂ))*f (u*v)*g (u*(v+h*z))*
      cutoff phi P mu v*cutoff phi P mu (v+h*z))=
      (f u*g u)*(∑v∈Icc 1 ⌊Y⌋₊,∑z∈Z,(c z/(z:ℂ))*f v*g (v+h*z)*
        cutoff phi P mu v*cutoff phi P mu (v+h*z))+(∑z∈Z,(c z/(z:ℂ))*E z) := by
    simp only [E,mul_sum]
    rw [Finset.sum_comm (s:=Z) (t:=Icc 1 ⌊Y⌋₊)]
    simp only [← sum_add_distrib]
    apply sum_congr rfl
    intro v hv
    apply sum_congr rfl
    intro z hz
    ring
  rw [heq]
  apply (norm_add_le _ _).trans
  have hfug : ‖f u*g u‖≤1 := by
    rw [norm_mul]
    exact (mul_le_mul (hf u) (hg u) (norm_nonneg _) (by positivity)).trans_eq (by norm_num)
  have hm : ‖(f u*g u)*(∑v∈Icc 1 ⌊Y⌋₊,∑z∈Z,(c z/(z:ℂ))*f v*g (v+h*z)*
        cutoff phi P mu v*cutoff phi P mu (v+h*z))‖≤C*B^(-10001/10000:ℝ)*Y := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right hfug (norm_nonneg _)).trans (by simpa using hY mu)
  nlinarith
end OrdinaryAnalyticCentering

end

end OAI
