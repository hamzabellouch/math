import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.RoughCube02
import OAI.Combinatorics.SumProduct.Alignment.RoughProduct02
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
noncomputable section
end
end
 

section
 
 

noncomputable section
namespace RoughCubeUniform
open RationalLattice MalcevCharacters RealPolynomialDegree RoughScales Filter
open RoughSourceExceptional

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {dim : ℕ}
variable (c : RealCoordinates G dim) (Γ : Subgroup G) [mtr : MetricSpace (G⧸Γ)]

 

theorem larger_scale_uniform (hsk : SecondKind c)
    (hΓ : ∀ g : G,g∈Γ ↔ ∀ i,∃ z : ℤ,c.coord g i=z)
    (htop : mtr.toUniformSpace.toTopologicalSpace=QuotientGroup.instTopologicalSpace Γ)
    (v D : ℕ) (c₀ C₀ : ℝ) (B : NNReal) (η : ℝ)
    (hc₀ : 0<c₀) (hC₀ : 0<C₀) (hB : 0<B) (hη : 0<η)
    (w : ℕ→ℕ) (S Z : ℕ→ℝ) (r L : ℕ→ℤ)
    (hw : Tendsto w atTop atTop) (hS : Tendsto S atTop atTop)
    (hZ : ∀ a : ℝ,0<a →Tendsto (fun n=>Z n/S n^a) atTop atTop)
    (hL : ∀ n,0<L n) (hsm : ∀ n,Smooth (w n) (L n))
    (hWL : ∀ n,(primorial (w n):ℤ)∣L n) (hr : ∀ n,(r n).natAbs.Coprime (primorial (w n)))
    (hSL : Tendsto (fun n=>S n/(L n:ℝ)) atTop atTop) :
    ∀ ε : ℝ,0<ε →∀ᶠ n in atTop,∀ Y : ℝ,Z n≤Y →
      ∀ P : (Fin (v+1)→ℝ)→G,(∀ i,HasDegree (fun y=>canonicalLog c (P y) i) D) →
      ((exceptional Γ v c₀ C₀ B η Y (S n) P (r n) (L n)).card:ℝ)/
        ((times (S n) (r n) (L n)).card:ℝ)<ε := by
  classical
  intro ε hε
  let fails (n : ℕ) (Y : ℝ) : Prop :=
    ∃ P : (Fin (v+1)→ℝ)→G,(∀ i,HasDegree (fun y=>canonicalLog c (P y) i) D) ∧
      ε≤((exceptional Γ v c₀ C₀ B η Y (S n) P (r n) (L n)).card:ℝ)/
        ((times (S n) (r n) (L n)).card:ℝ)
  have hs (n : ℕ) : ∃ Y : ℝ,Z n≤Y ∧ ((∃ Y,Z n≤Y ∧ fails n Y) → fails n Y) := by
    by_cases h : ∃ Y,Z n≤Y ∧ fails n Y
    · obtain ⟨Y,hY,hf⟩ := h
      exact ⟨Y,hY,fun _=>hf⟩
    · exact ⟨Z n,le_rfl,fun he=>(h he).elim⟩
  choose Y hY hsel using hs
  have hYsc : ∀ a : ℝ,0<a →Tendsto (fun n=>Y n/S n^a) atTop atTop := by
    intro a ha
    apply tendsto_atTop_mono' atTop ?_ (hZ a ha)
    filter_upwards [hS.eventually (eventually_ge_atTop 0)] with n hn
    exact div_le_div_of_nonneg_right (hY n) (Real.rpow_nonneg hn _)
  have hb := RoughCubeDensity.source_exceptional_decay c Γ hsk hΓ htop v D c₀ C₀ B η
    hc₀ hC₀ hB hη w S Y r L hw hS hYsc hL hsm hWL hr hSL ε hε
  filter_upwards [hb] with n hn
  intro z hz P hP
  by_contra! he
  obtain ⟨Q,hQ,hbad⟩ := hsel n ⟨z,hz,P,hP,he⟩
  exact (not_lt_of_ge hbad) (hn Q hQ)

end RoughCubeUniform
end
end
 

section
 
 

noncomputable section
namespace RoughProductRemoval
open Filter
open scoped BigOperators

lemma power_domination_nonneg {T Z : ℕ → ℝ}
    (hT : ∀ᶠ n in atTop,0<T n)
    (hZ : ∀ a : ℝ,0<a →Tendsto (fun n=>Z n/T n^a) atTop atTop) :
    ∀ᶠ n in atTop,0≤Z n := by
  filter_upwards [hT,(hZ 1 zero_lt_one).eventually (eventually_ge_atTop 0)] with n ht hz
  simp only [Real.rpow_one] at hz
  simpa only [div_mul_cancel₀ _ ht.ne'] using mul_nonneg hz ht.le

lemma domination_smaller {S T Z : ℕ → ℝ}
    (hS : ∀ᶠ n in atTop,0<S n) (hST : ∀ᶠ n in atTop,S n≤T n)
    (hZ : ∀ a : ℝ,0<a →Tendsto (fun n=>Z n/T n^a) atTop atTop) :
    ∀ a : ℝ,0<a →Tendsto (fun n=>Z n/S n^a) atTop atTop := by
  have hT : ∀ᶠ n in atTop,0<T n := by filter_upwards [hS,hST] with n h₁ h₂; exact h₁.trans_le h₂
  have hz:=power_domination_nonneg hT hZ
  intro a ha
  apply tendsto_atTop_mono' atTop ?_ (hZ a ha)
  filter_upwards [hS,hST,hz] with n hs ht hn
  exact div_le_div_of_nonneg_left hn (Real.rpow_pos_of_pos hs _) (Real.rpow_le_rpow hs.le ht ha.le)

lemma residual_power_domination {S T Z : ℕ → ℝ}
    (hS : ∀ᶠ n in atTop,0<S n) (hST : ∀ᶠ n in atTop,S n≤T n)
    (hZ : ∀ a : ℝ,0<a →Tendsto (fun n=>Z n/T n^a) atTop atTop)
    (d m : ℕ) (hd : 0<d) :
    ∀ a : ℝ,0<a →Tendsto (fun n=>(Z n/((d:ℝ)*(2*T n)^m))/S n^a) atTop atTop := by
  have hT : ∀ᶠ n in atTop,0<T n := by filter_upwards [hS,hST] with n h₁ h₂; exact h₁.trans_le h₂
  have hz:=power_domination_nonneg hT hZ
  have hc : (0:ℝ)<(d:ℝ)*2^m := by positivity
  intro a ha
  have ht := (hZ (a+m) (by positivity)).atTop_div_const hc
  apply tendsto_atTop_mono' atTop ?_ ht
  filter_upwards [hS,hST,hz] with n hs hst hzn
  have htpos : 0<T n := hs.trans_le hst
  have he : (Z n/T n^(a+(m:ℝ)))/((d:ℝ)*2^m)=
      (Z n/((d:ℝ)*(2*T n)^m))/T n^a := by
    rw [Real.rpow_add htpos,Real.rpow_natCast,mul_pow]
    field_simp
  rw [he]
  exact div_le_div_of_nonneg_left (by positivity) (Real.rpow_pos_of_pos hs _)
    (Real.rpow_le_rpow hs.le hst ha.le)

def totalScale {m : ℕ} (S : Fin m → ℝ) : ℝ := 1+∑ j,S j

lemma totalScale_succ {m : ℕ} (S : Fin (m+1) → ℝ) :
    totalScale S = S 0+totalScale (Fin.tail S) := by
  simp only [totalScale,Fin.sum_univ_succ,Fin.tail]
  ring

lemma totalScale_bounds {m : ℕ} (S : Fin m → ℝ) (hS : ∀ j,0≤S j) :
    1≤totalScale S ∧ ∀ j,S j≤totalScale S := by
  have hh : (0:ℝ)≤∑ j,S j := Finset.sum_nonneg (fun j _=>hS j)
  refine ⟨by dsimp [totalScale]; linarith,?_⟩
  intro j
  have hj:=Finset.single_le_sum (fun i _=>hS i) (Finset.mem_univ j)
  dsimp [totalScale]
  linarith

lemma totalScale_pos_eventually {m : ℕ} (S : ℕ → Fin m → ℝ)
    (hS : ∀ j,Tendsto (fun n=>S n j) atTop atTop) :
    ∀ᶠ n in atTop,1≤totalScale (S n) := by
  have h := eventually_all.mpr (fun j=>(hS j).eventually (eventually_ge_atTop 0))
  filter_upwards [h] with n hn
  exact (totalScale_bounds (S n) hn).1

lemma tail_domination {m : ℕ} (S : ℕ → Fin (m+1) → ℝ) (Z : ℕ → ℝ)
    (hS : ∀ j,Tendsto (fun n=>S n j) atTop atTop)
    (hZ : ∀ a : ℝ,0<a →Tendsto (fun n=>Z n/(totalScale (S n))^a) atTop atTop) :
    ∀ a : ℝ,0<a →Tendsto (fun n=>Z n/(totalScale (Fin.tail (S n)))^a) atTop atTop := by
  apply domination_smaller ?_ ?_ hZ
  · filter_upwards [totalScale_pos_eventually (fun n=>Fin.tail (S n)) (fun j=>hS j.succ)] with n hn
    linarith
  · filter_upwards [(hS 0).eventually (eventually_ge_atTop 0)] with n hn
    rw [totalScale_succ]
    linarith

lemma product_tail_bound {m : ℕ} (S : Fin (m+1) → ℝ) (t : Fin m → ℤ)
    (hS : ∀ j,0≤S j) (ht : ∀ j,0<t j ∧ (t j:ℝ)<2*S j.succ) :
    (0:ℝ)<(∏ j,(t j).natAbs:ℕ) ∧
      ((∏ j,(t j).natAbs:ℕ):ℝ)≤(2*totalScale S)^m := by
  have hp : ∀ j,0<(t j).natAbs := fun j=>Int.natAbs_pos.mpr (ht j).1.ne'
  constructor
  · exact_mod_cast (Finset.prod_pos (fun j _=>hp j))
  · rw [Nat.cast_prod]
    calc
      (∏ j,((t j).natAbs:ℝ)) ≤ ∏ _j : Fin m,(2*totalScale S) := by
        apply Finset.prod_le_prod₀ (fun j _=>by positivity)
        intro j _
        have he : ((t j).natAbs:ℝ)=(t j:ℝ) := by
          rw [← Int.cast_natCast,Int.natCast_natAbs,(abs_of_pos (ht j).1)]
        rw [he]
        exact (ht j).2.le.trans (mul_le_mul_of_nonneg_left ((totalScale_bounds S hS).2 j.succ) (by norm_num))
      _=(2*totalScale S)^m := by simp

end RoughProductRemoval
end
end
 

section
 
 

noncomputable section
namespace RoughProductRemoval
open RationalLattice MalcevCharacters RealPolynomialDegree RoughScales Filter
open RoughSamplingWeights FinitePieceAverages RoughSourceExceptional
open scoped BigOperators
attribute [local instance] Classical.propDecidable

lemma filter_union_bound {α β : Type*} [DecidableEq α] [Fintype β]
    (S : Finset α) (H : α → Prop) (E : β → α → Prop) (a : ℝ)
    (hH : ∀ x∈S,H x →∃ b,E b x)
    (hE : ∀ b,((S.filter (E b)).card:ℝ)≤a) :
    ((S.filter H).card:ℝ)≤(Fintype.card β:ℝ)*a := by
  classical
  have hs : S.filter H ⊆ Finset.univ.biUnion (fun b=>S.filter (E b)) := by
    intro x hx
    obtain ⟨hx,h⟩ := Finset.mem_filter.mp hx
    obtain ⟨b,hb⟩ := hH x hx h
    exact Finset.mem_biUnion.mpr ⟨b,Finset.mem_univ _,Finset.mem_filter.mpr ⟨hx,hb⟩⟩
  have hc := (Finset.card_le_card hs).trans (Finset.card_biUnion_le)
  have hc' : ((S.filter H).card:ℝ)≤∑ b : β,((S.filter (E b)).card:ℝ) := by
    exact_mod_cast hc
  exact hc'.trans (by simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using Finset.sum_le_sum (s:=Finset.univ) (fun b _=>hE b))

lemma smooth_nat_coprime_rough {w M : ℕ} {t : ℤ} (hM : Smooth w (M:ℤ))
    (ht : Rough w t) : M.Coprime t.natAbs := by
  simpa only [Int.natAbs_natCast] using
    (Int.isCoprime_iff_nat_coprime.mp (coprime_smooth_rough hM ht))

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {dim : ℕ}
variable (c : RealCoordinates G dim) (Γ : Subgroup G) [mtr : MetricSpace (G⧸Γ)]

 

omit [IsTopologicalGroup G] in
theorem firstBad_card_bound {m v D : ℕ} {c₀ C₀ : ℝ} {B : NNReal} {η Z S Y δ : ℝ}
    (d M : ℕ) (hd : 0<d) (hC : 0≤C₀) (A : Fin v → ℤ)
    (P : (Fin ((m+1)+v)→ℝ)→G)
    (hP : ∀ i,HasDegree (fun y=>canonicalLog c (P y) i) D)
    (t : Fin m → ℤ) (ht : ∀ j,0<t j)
    (hdq : d.Coprime (∏ j,(t j).natAbs)) (hMq : M.Coprime (∏ j,(t j).natAbs))
    (hZ : ((d*(∏ j,(t j).natAbs):ℕ):ℝ)≤Z)
    (hY : Y≤Z/(d*(∏ j,(t j).natAbs):ℕ)) (r L : ℤ)
    (htimes : ∀ s∈times S r L,0<s ∧ (M*d).Coprime s.natAbs)
    (huni : ∀ Y',Y≤Y' →∀ Q : (Fin (v+1)→ℝ)→G,
      (∀ i,HasDegree (fun y=>canonicalLog c (Q y) i) D) →
      ((exceptional Γ v c₀ (C₀+1) B η Y' S Q r L).card:ℝ)≤δ*(times S r L).card) :
    (((times S r L).filter (fun s=>firstBad Γ m v c₀ C₀ B η Z d M A P s t)).card:ℝ)≤
      (d:ℝ)^v*δ*(times S r L).card := by
  classical
  obtain ⟨Q,hQ,hred⟩ := firstBad_reduction Γ c d M hd hC A P hP t ht hdq hMq hZ
  have hh := filter_union_bound (times S r L)
    (fun s=>firstBad Γ m v c₀ C₀ B η Z d M A P s t)
    (fun R s=>RoughProgressionDensity.BadAt Γ v c₀ (C₀+1) B η
      (Z/(d*(∏ j,(t j).natAbs):ℕ)) (Q R) s) (δ*(times S r L).card)
    (fun s hs h=>hred s (htimes s hs).1 (htimes s hs).2 h)
    (fun R=>huni _ hY (Q R) (hQ R))
  simpa only [Fintype.card_fun,Fintype.card_fin,Nat.cast_pow,mul_assoc] using hh

 

theorem firstBad_fiber_eventual (hsk : SecondKind c)
    (hΓ : ∀ g : G,g∈Γ ↔ ∀ i,∃ z : ℤ,c.coord g i=z)
    (htop : mtr.toUniformSpace.toTopologicalSpace=QuotientGroup.instTopologicalSpace Γ)
    (m v D d : ℕ) (hd : 0<d) (c₀ C₀ : ℝ) (B : NNReal) (η : ℝ)
    (hc₀ : 0<c₀) (hC₀ : 0<C₀) (hB : 0<B) (hη : 0<η)
    (w M : ℕ→ℕ) (S : ℕ → Fin (m+1) → ℝ) (Z : ℕ→ℝ)
    (r : ℕ → Fin (m+1) → ℤ) (L : ℕ→ℤ)
    (hw : Tendsto w atTop atTop) (hS : ∀ j,Tendsto (fun n=>S n j) atTop atTop)
    (hZ : ∀ a : ℝ,0<a →Tendsto (fun n=>Z n/(totalScale (S n))^a) atTop atTop)
    (hMs : ∀ n,Smooth (w n) (M n:ℤ))
    (hL : ∀ n,0<L n) (hsm : ∀ n,Smooth (w n) (L n))
    (hWL : ∀ n,(primorial (w n):ℤ)∣L n)
    (hr : ∀ n j,(r n j).natAbs.Coprime (primorial (w n)))
    (hSL : ∀ j,Tendsto (fun n=>S n j/(L n:ℝ)) atTop atTop) :
    ∀ ε : ℝ,0<ε →∀ᶠ n in atTop,
      ∀ (A : Fin v → ℤ) (P : (Fin ((m+1)+v)→ℝ)→G),
      (∀ i,HasDegree (fun y=>canonicalLog c (P y) i) D) →
      ∀ t∈productTimes (Fin.tail (S n)) (Fin.tail (r n)) (L n),
      (((times (S n 0) (r n 0) (L n)).filter
        (fun s=>firstBad Γ m v c₀ C₀ B η (Z n) d (M n) A P s t)).card:ℝ)≤
          ε*(times (S n 0) (r n 0) (L n)).card := by
  classical
  intro ε hε
  let U (n : ℕ) := Z n/((d:ℝ)*(2*totalScale (S n))^m)
  have hSP := eventually_all.mpr (fun j=>(hS j).eventually (eventually_gt_atTop 0))
  have hST : ∀ᶠ n in atTop,S n 0≤totalScale (S n) := by
    filter_upwards [hSP] with n hn
    exact (totalScale_bounds _ (fun j=>(hn j).le)).2 0
  have hU := residual_power_domination ((hS 0).eventually (eventually_gt_atTop 0)) hST hZ d m hd
  have hUtop : Tendsto U atTop atTop := by
    simpa only [pow_zero,div_one] using integer_scales_of_real (hS 0) hU 0
  have hdv : (0:ℝ)<(d:ℝ)^v := pow_pos (by exact_mod_cast hd) _
  have huni := RoughCubeUniform.larger_scale_uniform c Γ hsk hΓ htop v D c₀ (C₀+1) B η
    hc₀ (by linarith) hB hη w (fun n=>S n 0) U (fun n=>r n 0) L hw (hS 0) hU
    hL hsm hWL (fun n=>hr n 0) (hSL 0) (ε/(d:ℝ)^v) (div_pos hε hdv)
  have hcard := timeLength_tendsto (r:=fun n=>r n 0) hL (hS 0) (hSL 0)
  filter_upwards [huni,hSP,hw.eventually (eventually_ge_atTop d),
    hUtop.eventually (eventually_ge_atTop 1),hcard.eventually (eventually_gt_atTop 0)] with n hn hsn hwn hun hcn
  intro A P hP t ht
  have htt : ∀ j,t j∈times (S n j.succ) (r n j.succ) (L n) := by
    simpa only [productTimes,Fintype.mem_piFinset,Fin.tail] using ht
  have htdata (j : Fin m) := time_positive_rough (hsn j.succ) (hL n) (hr n j.succ) (hWL n) (htt j)
  have hb := product_tail_bound (S n) t (fun j=>(hsn j).le)
    (fun j=>⟨(htdata j).1,(htdata j).2.2⟩)
  have hdq : d.Coprime (∏ j,(t j).natAbs) := Nat.Coprime.prod_right (fun j _=>
    period_coprime_of_rough (w n) d (t j).natAbs hd hwn
      ((rough_iff_coprime _ _).mp (htdata j).2.1))
  have hMq : (M n).Coprime (∏ j,(t j).natAbs) := Nat.Coprime.prod_right
    (fun j _=>smooth_nat_coprime_rough (hMs n) (htdata j).2.1)
  have hden : (0:ℝ)<(d:ℝ)*(2*totalScale (S n))^m := by
    have hh := (totalScale_bounds (S n) (fun j=>(hsn j).le)).1
    positivity
  have hZn : 0≤Z n := by
    have hh := (le_div_iff₀ hden).mp hun
    dsimp [U] at hun
    have hh' := (le_div_iff₀ hden).mp hun
    linarith
  have hKpos : (0:ℝ)<((d*(∏ j,(t j).natAbs):ℕ):ℝ) := by
    rw [Nat.cast_mul]
    exact mul_pos (by exact_mod_cast hd) hb.1
  have hKle : ((d*(∏ j,(t j).natAbs):ℕ):ℝ)≤(d:ℝ)*(2*totalScale (S n))^m := by
    rw [Nat.cast_mul]
    exact mul_le_mul_of_nonneg_left hb.2 (by positivity)
  have hY : U n≤Z n/(d*(∏ j,(t j).natAbs):ℕ) :=
    div_le_div_of_nonneg_left hZn hKpos hKle
  have hKZ : ((d*(∏ j,(t j).natAbs):ℕ):ℝ)≤Z n := by
    have hh := (le_div_iff₀ hKpos).mp (hun.trans hY)
    simpa using hh
  have hcpos : (0:ℝ)<(times (S n 0) (r n 0) (L n)).card := by
    rw [times_card _ _ _ (hL n)]
    exact hcn
  have hbound := firstBad_card_bound c Γ d (M n) hd hC₀.le A P hP t
    (fun j=>(htdata j).1) hdq hMq hKZ hY (r n 0) (L n) (fun s hs=>by
      have hh:=time_positive_rough (hsn 0) (hL n) (hr n 0) (hWL n) hs
      exact ⟨hh.1,(smooth_nat_coprime_rough (hMs n) hh.2.1).mul_left
        (period_coprime_of_rough (w n) d s.natAbs hd hwn ((rough_iff_coprime _ _).mp hh.2.1))⟩)
    (fun Y hY Q hQ=>((div_lt_iff₀ hcpos).mp (hn Y hY Q hQ)).le)
  convert hbound using 1
  field_simp

end RoughProductRemoval

end
end

end OAI
