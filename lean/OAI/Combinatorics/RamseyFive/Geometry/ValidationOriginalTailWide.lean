import Mathlib
import OAI.Combinatorics.SharpRamsey.Entropy.LargeCard
import OAI.Combinatorics.RamseyFive.Decoding.SumDiagonal
import OAI.Combinatorics.RamseyFive.Geometry.SampledPoints
import OAI.Combinatorics.RamseyFive.Geometry.MassHyperplane
import OAI.Combinatorics.RamseyFive.Geometry.AbsModifiedPointScore
import OAI.Combinatorics.RamseyFive.Probability.MomentTailRatio
import OAI.Combinatorics.RamseyFive.Entropy.ValidationBudgetWide

namespace OAI

noncomputable section
namespace SharpRamseyFive.ScoreGeometry

section
open Module ProjectiveIncidence CellVariance ScoreRegularity
open MeasureTheory ProbabilityTheory PoissonScore
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  (x : ℙ K V) [Fintype (RadialLine x)]

theorem validation_original_tail_wide {d : ℕ} (hdim : finrank K V=d+1) (hd : 1≤d)
    {J : Type} [Fintype J] (S : Finset (ℙ K V)) (C : J→Finset (ℙ K V))
    (hS : S.Nonempty) (a b c : J) (ha : C a⊆S) (hb : C b⊆S) (hc : C c=C a∩C b)
    (F : Finset (ℙ K (Dual K V)))
    (hF : ∀ H∈F,Incident x H ∧ H∉exceptional S C)
    (hf : ownFraction S (C a) (C b)≤2/25)
    (hn : (Nat.card K:ℝ)/S.card ≤1/100)
    (L : ℝ≥0) (R : ℕ) (hR : 201≤R)
    (hP : 100000≤(L:ℝ)*R) (hL : 1≤(L:ℝ))
    (hRsmall : (R:ℝ)≤((L:ℝ)*R)/100000)
    (hLR : 100*(L:ℝ)≤(L:ℝ)*R)
    (hlog : (R:ℝ)*Real.log (L:ℝ)≤((L:ℝ)*R)/100)
    (hx : x∉irregular (d:=d) S C ((L:ℝ)/100))
    (hcard : (F.card:ℝ)≤400*(scale (K:=K) d S.card)^2)
    (htail : ∀ u : ℝ,0<u → u≤2 →
      ((Finset.univ.filter fun z : {z : F×F // z.1≠z.2} =>
        u ≤ mass (radialWeight x (outsideAt x S (C a∪C b)) (pointStrength S))
          (pencilLines x F z.val.1∩pencilLines x F z.val.2)).card:ℝ)*u^200 ≤
      (scale (K:=K) d S.card)^2*Real.exp (((L:ℝ)*R)/50))
    {κ t : ℝ} (hκ : κ+Real.log 10≤((L:ℝ)*R)/20)
    (ht : scale (K:=K) d S.card*Real.exp (-κ)/10≤t) :
    (scheduleMeasure (fun _ : S => L*pointStrength S) R).real
      {ω | Unsampled x S ω ∧ t < |pointScore S (C a∪C b) F
        (Real.exp (-(L:ℝ)*(1-ownFraction S (C a) (C b)))) ω|} ≤
      Real.exp (-((L:ℝ)*R)/2) := by
  let B : ℝ := scale (K:=K) d S.card
  let θ := fun H H' : F => mass
    (radialWeight x (outsideAt x S (C a∪C b)) (pointStrength S))
      (pencilLines x F H∩pencilLines x F H')
  have hB : 0<B := by
    dsimp [B,scale]
    have hq : (0:ℝ)<Nat.card K := by exact_mod_cast (Nat.card_pos (α:=K))
    have hsn : (0:ℝ)<S.card := by exact_mod_cast hS.card_pos
    positivity
  have hξ : 0≤(L:ℝ)/100 := by positivity
  have ht0 : 0<B*Real.exp (-κ)/10 := by positivity
  have hb0 : Real.exp (-(L:ℝ)*(1-ownFraction S (C a) (C b)))∈Set.Icc 0 1 := by
    refine ⟨(Real.exp_pos _).le,Real.exp_le_one_iff.mpr ?_⟩
    have : 0≤1-ownFraction S (C a) (C b) := by linarith only [hf]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr L.coe_nonneg) this
  have hθ0 : ∀H H',0≤θ H H' := fun _ _ => mass_nonneg _ _
  have hθ2 : ∀H H',θ H H'≤2 := by
    intro H H'
    have hm := actual_radial_mass_bounds x S C hS a b c ha hb hc F hF hf hn
    have hsub : θ H H' ≤ mass
        (radialWeight x (outsideAt x S (C a∪C b)) (pointStrength S)) (pencilLines x F H) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.inter_subset_left)
        (fun _ _ _ => NNReal.coe_nonneg _)
    exact hsub.trans (by linarith only [(hm H).2.2])
  have hov := ValidationBounds.overlap_power_sum θ hθ0 hθ2
    (B^2*Real.exp (((L:ℝ)*R)/50)) (400*B^2) (by positivity)
    (by simpa only [Fintype.card_coe] using hcard) 200 R hR (by
      intro u hu hu2
      convert! htail u hu hu2 using 1
      congr 3
      ext z
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      rfl)
  have hs : (∑H:F,∑H'∈Finset.univ.erase H,θ H H'^R)≤∑H:F,∑H':F,θ H H'^R := by
    apply Finset.sum_le_sum
    intro H _
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
      (fun H' _ _ => pow_nonneg (hθ0 H H') R)
  have hDS := ValidationBounds.validation_budget_wide hP hRsmall hLR
    (40*B*Real.exp ((L:ℝ)/100)) _ (by positivity)
    (by nlinarith only [mul_nonneg hB.le (Real.exp_pos ((L:ℝ)/100)).le]) (hs.trans hov)
  have hv := actual_original_validation x hdim hd S C hS a b c ha hb hc F hF hf hn hξ hx
    L hL R (by omega)
  have hbudget := ValidationBounds.final_validation_budget_wide hP hL rfl hRsmall hlog
    hcard (Nat.cast_nonneg F.card) hDS
  have hm : (∫ω,(modifiedPointScore x S (C a∪C b) F
      (Real.exp (-(L:ℝ)*(1-ownFraction S (C a) (C b)))) ω)^2
      ∂scheduleMeasure (fun _ : S => L*pointStrength S) R)≤B^2*Real.exp (-3*((L:ℝ)*R)/5) :=
    hv.trans hbudget
  have hprob := unsampled_moment_tail x S (C a∪C b) (fun _ : S => L*pointStrength S)
    F hb0 (show Even 2 by decide) ht0 hm
  have herr := ScoreScalars.validation_tail_ratio hB hκ
  apply (measureReal_mono (μ:=scheduleMeasure (fun _ : S => L*pointStrength S) R)
    ?_ (measure_ne_top _ _)).trans (hprob.trans herr)
  intro ω hω
  exact ⟨hω.1,ht.trans_lt hω.2⟩

end

open Module ProjectiveIncidence CellVariance ScoreRegularity
open MeasureTheory ProbabilityTheory PoissonScore
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] in
lemma typicalFailures_mono (U S : Finset (ℙ K V)) (O : ℙ K V→Finset (ℙ K V))
    (E : Finset (ℙ K (Dual K V))) (b : ℙ K V→ℝ) {s t : ℝ} (hst : s≤t)
    {R : ℕ} (ω : Fin R→S→ℕ) : typicalFailures U S O E b t ω⊆typicalFailures U S O E b s ω := by
  intro x hx
  obtain ⟨hx,hu,ht⟩ := Finset.mem_filter.mp hx
  exact Finset.mem_filter.mpr ⟨hx,hu,hst.trans_lt ht⟩

omit [Finite K] [FiniteDimensional K V] in
lemma integral_typicalFailures_tail (U S : Finset (ℙ K V)) (O : ℙ K V→Finset (ℙ K V))
    (E : Finset (ℙ K (Dual K V))) (b : ℙ K V→ℝ) (t : ℝ) {R : ℕ} (rate : S→ℝ≥0)
    {B a : ℝ} (ha : 0<a)
    (hB : (∫ω,((typicalFailures U S O E b t ω).card:ℝ) ∂scheduleMeasure rate R)≤B) :
    (scheduleMeasure rate R).real {ω | a≤((typicalFailures U S O E b t ω).card:ℝ)}≤B/a := by
  apply (le_div_iff₀ ha).mpr
  rw [mul_comm]
  exact (mul_meas_ge_le_integral_of_nonneg (Filter.Eventually.of_forall
    (fun ω => Nat.cast_nonneg (typicalFailures U S O E b t ω).card))
    (by
      apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable (U.card:ℝ)
      exact Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg _)]
        exact Nat.cast_le.mpr (Finset.card_filter_le _ _)) a).trans hB

omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] in
lemma sampleMean_uniform (S : Finset (ℙ K V)) (hS : S.Nonempty) (L : ℝ≥0) (R : ℕ) :
    (R:ℝ)*(∑_i:S,(L*pointStrength S:ℝ≥0):ℝ)=(Nat.card K:ℝ)*((L:ℝ)*R) := by
  have hn : (S.card:ℝ)≠0 := (Nat.cast_pos.mpr hS.card_pos).ne'
  simp only [NNReal.coe_mul,coe_pointStrength,Finset.sum_const,Finset.card_univ,
    Fintype.card_coe,nsmul_eq_mul]
  field_simp

theorem original_score_procedure {d : ℕ} (hdim : finrank K V=d+1) (hd : 1≤d)
    (hq : (10:ℝ)≤Nat.card K) (U S : Finset (ℙ K V)) (hSU : S⊆U) (hS : S.Nonempty)
    (O : ℙ K V→Finset (ℙ K V)) (E T : Finset (ℙ K (Dual K V)))
    (hT : T.Nonempty) (hTE : T⊆E) (b : ℙ K V→ℝ) (bad : Finset (ℙ K V))
    (L : ℝ≥0) (R : ℕ) (a M : ℝ)
    (hsmall : ∀H∈T,cellMass S ((Nat.card K:ℝ)/S.card) H≤a)
    (hM : ∑H∈E,cellMass S ((Nat.card K:ℝ)/S.card) H≤M)
    (βS βU γS γU : ℝ) (hγS : 0<γS) (hγU : 0<γU)
    (hb : ∀x∈U\bad,b x∈Set.Icc 0 1)
    (hc : ∀x∈U\bad,(9/10:ℝ)≤(1-b x)^R)
    (herr : ∀x∈U\bad,b x*(pencil x∩E).card≤
      ((T.card:ℝ)*Real.exp (-((R:ℝ)*(L:ℝ))*a)/2)/(100*(Nat.card K:ℝ)))
    (htrain : (∫ω,((typicalFailures S S O E b
      (((T.card:ℝ)*Real.exp (-((R:ℝ)*(L:ℝ))*a)/2)/(10*(Nat.card K:ℝ))) ω).card:ℝ)
      ∂scheduleMeasure (fun _ : S => L*pointStrength S) R)≤βS)
    (hamb : (∫ω,((typicalFailures U S O E b
      (((T.card:ℝ)*Real.exp (-((R:ℝ)*(L:ℝ))*a)/2)/(10*(Nat.card K:ℝ))) ω).card:ℝ)
      ∂scheduleMeasure (fun _ : S => L*pointStrength S) R)≤βU) :
    let P := (L:ℝ)*R
    let zmin := (T.card:ℝ)*Real.exp (-P*a)/2
    Real.exp (-P*a)/2-M*Real.exp (-P/2000)/((1/2000:ℝ)*zmin)-βS/γS-βU/γU-
      Real.exp (-((Nat.card K:ℝ)*P)/4) ≤
    (scheduleMeasure (fun _ : S => L*pointStrength S) R).real
      {ω | let W := decoded U S O b (emptyTests E (hyperplaneSupport S) ω).card ω
        (sampleCount ω:ℝ)≤2*((Nat.card K:ℝ)*P) ∧
        (W.card:ℝ)≤2*((Nat.card K:ℝ)*P)+bad.card+γU+100*(Nat.card K:ℝ)^(d+1)/zmin ∧
        (99/100:ℝ)*S.card-bad.card-γS≤((W∩S).card:ℝ)} := by
  dsimp only
  let P : ℝ := (L:ℝ)*R
  let zmin : ℝ := (T.card:ℝ)*Real.exp (-P*a)/2
  let q : ℝ := Nat.card K
  let μ := scheduleMeasure (fun _ : S => L*pointStrength S) R
  let Z := fun ω : Fin R→S→ℕ => emptyTests E (hyperplaneSupport S) ω
  let t : ℝ := zmin/(10*q)
  let A := {ω : Fin R→S→ℕ | zmin≤((Z ω).card:ℝ) ∧
    emptyWeight E (hyperplaneSupport S) (fun H => cellMass S (q/S.card) H) ω≤((Z ω).card:ℝ)/1000}
  let B := {ω : Fin R→S→ℕ | γS≤((typicalFailures S S O E b t ω).card:ℝ)}
  let C := {ω : Fin R→S→ℕ | γU≤((typicalFailures U S O E b t ω).card:ℝ)}
  let D := {ω : Fin R→S→ℕ | 2*(q*P)≤(sampleCount ω:ℝ)}
  have hq0 : 0<q := by dsimp [q];linarith only [hq]
  have hz0 : 0<zmin := by
    dsimp [zmin]
    have : (0:ℝ)<T.card := Nat.cast_pos.mpr hT.card_pos
    positivity
  have hm (H : ℙ K (Dual K V)) :
      mass (fun _ : S => pointStrength S) (hyperplaneSupport S H)=cellMass S (q/S.card) H := by
    rw [mass_hyperplaneSupport,coe_pointStrength]
  have hPa : (R:ℝ)*(L:ℝ)=P := by dsimp [P];ring
  have hA : Real.exp (-P*a)/2-M*Real.exp (-P/2000)/((1/2000:ℝ)*zmin)≤μ.real A := by
    have he := emptyTests_many_small (R:=R) L (fun _ : S => pointStrength S) E T hT hTE
      (hyperplaneSupport S) (a:=a) (c:=1/2000) (b:=1/2000) (M:=M)
      (by norm_num) (by norm_num) (fun H hH => by rw [hm];exact hsmall H hH)
      (by simp_rw [hm];exact hM)
    dsimp only at he
    rw [hPa] at he
    simp_rw [hm] at he
    convert! he using 1 <;> dsimp [zmin,μ,A,Z] <;> congr 2 <;> ring_nf
  have hB : μ.real B≤βS/γS := integral_typicalFailures_tail S S O E b t _ hγS (by
    simpa only [hPa] using htrain)
  have hC : μ.real C≤βU/γU := integral_typicalFailures_tail U S O E b t _ hγU (by
    simpa only [hPa] using hamb)
  have hD : μ.real D≤Real.exp (-(q*P)/4) := by
    have he := sampleCount_double_tail (fun _ : S => L*pointStrength S) R
    rw [sampleMean_uniform S hS L R] at he
    exact he
  apply (intersect_three_success μ A B C D hA hB hC hD).trans
  apply measureReal_mono _ (measure_ne_top _ _)
  intro ω hω
  obtain ⟨hAω,hbad⟩ := hω
  have hz : zmin≤((Z ω).card:ℝ) := hAω.1
  have hZZ : (Z ω).Nonempty := Finset.card_pos.mp (by exact_mod_cast hz0.trans_le hz)
  have hBω : ((typicalFailures S S O E b t ω).card:ℝ)<γS := lt_of_not_ge
    (fun h => hbad (Or.inl (Or.inl h)))
  have hCω : ((typicalFailures U S O E b t ω).card:ℝ)<γU := lt_of_not_ge
    (fun h => hbad (Or.inl (Or.inr h)))
  have hDω : (sampleCount ω:ℝ)<2*(q*P) := lt_of_not_ge
    (fun h => hbad (Or.inr h))
  have ht : t≤((Z ω).card:ℝ)/(10*q) := div_le_div_of_nonneg_right hz (by positivity)
  have hTS : ((typicalFailures S S O E b (((Z ω).card:ℝ)/(10*q)) ω).card:ℝ)≤γS :=
    (Nat.cast_le.mpr (Finset.card_le_card (typicalFailures_mono S S O E b ht ω))).trans hBω.le
  have hTU : ((typicalFailures U S O E b (((Z ω).card:ℝ)/(10*q)) ω).card:ℝ)≤γU :=
    (Nat.cast_le.mpr (Finset.card_le_card (typicalFailures_mono U S O E b ht ω))).trans hCω.le
  have hbound := decoded_bounds hdim hd hq U S hSU hS O E b ω bad hZZ
    (by simpa only [emptyWeight_eq_sum] using hAω.2) hb hc (fun x hx => (herr x hx).trans (by
      rw [hPa]
      exact div_le_div_of_nonneg_right hz (by positivity)))
  dsimp only at hbound
  have hdiv : 100*q^(d+1)/((Z ω).card:ℝ)≤100*q^(d+1)/zmin :=
    div_le_div_of_nonneg_left (by positivity) hz0 hz
  change (sampleCount ω:ℝ)≤2*(q*P) ∧ _
  refine ⟨hDω.le,?_,?_⟩
  all_goals dsimp only [q,P,zmin,Z] at hDω hTU hTS hdiv
  · linarith only [hbound.2,hDω,hTU,hdiv]
  · linarith only [hbound.1,hTS]

end SharpRamseyFive.ScoreGeometry

end

end OAI
