import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.ObservableProducts
import OAI.GroupTheory.SimpleAmenable.RandomFields.TransportEstimate

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section JointBitField
open Classical MeasureTheory Filter
open scoped Topology

noncomputable def jointBitFieldLaw {k a m D : ℕ} (v : Fin k → ℝ×ℝ)
    (S : Fin k → FieldSignalData) (hD : 0<D) (η κ : ℝ) (n : ℕ) :
    Measure (∀j,FlagSite a m D (v j) → Bool) :=
  Measure.pi (fun j => (S j).bitLaw (a:=a) (m:=m) (v:=v j) hD η κ n)

instance jointBitFieldLaw_probability {k a m D : ℕ} (v : Fin k → ℝ×ℝ)
    (S : Fin k → FieldSignalData) (hD : 0<D) (η κ : ℝ) (n : ℕ) :
    IsProbabilityMeasure (jointBitFieldLaw (a:=a) (m:=m) v S hD η κ n) := by
  unfold jointBitFieldLaw
  infer_instance

noncomputable def jointBitReindex {k a m D : ℕ} (v : Fin k → ℝ×ℝ)
    (hD : 0<D) (g : polygonFullGroup a m) :
    (∀j,FlagSite a m D (v j) → Bool) → (∀j,FlagSite a m D (v j) → Bool) :=
  fun b j => bitReindex (flagSitePermutation hD g) (b j)

theorem jointBitReindex_measurable {k a m D : ℕ} (v : Fin k → ℝ×ℝ)
    (hD : 0<D) (g : polygonFullGroup a m) : Measurable (jointBitReindex v hD g) :=
  Measurable.of_eval (fun j => (bitReindex_measurable _).comp (measurable_pi_apply j))

theorem finiteSignalFields_transport {k a m D : ℕ} (v : Fin k → ℝ×ℝ)
    (S : Fin k → FieldSignalData) (hD : 0<D) (F : Finset (polygonFullGroup a m))
    {ε : ℝ} (hε : 0<ε) :
    ∃η κ : ℝ,0<η ∧ η≤1 ∧ 0<κ ∧ ∀ᶠn : ℕ in atTop,∀g∈F,∀j,
      ObservableClose ((S j).bitLaw (v:=v j) hD η κ n)
        (((S j).bitLaw (v:=v j) hD η κ n).map (bitReindex (flagSitePermutation hD g))) ε := by
  choose C₁ C₂ hC₁ hC₂ ht using
    (fun i : Fin k×F => (S i.1).bitLaw_transport_constants (v:=v i.1) hD i.2.val)
  let A := ∑i,C₁ i
  let B := ∑i,C₂ i
  have hA : 0≤A := Finset.sum_nonneg (fun i _ => hC₁ i)
  have hB : 0≤B := Finset.sum_nonneg (fun i _ => hC₂ i)
  obtain ⟨η,κ,δ,d,hη,hη₁,hκ,hδ,hd,hsmall⟩ :=
    smallTransportParameters smoothNoiseTransportConstant_pos hA hB hε
  refine ⟨η,κ,hη,hη₁,hκ,?_⟩
  have hh : ∀ᶠn : ℕ in atTop,∀i : Fin k×F,
      ObservableClose ((S i.1).bitLaw (v:=v i.1) hD η κ n)
        (((S i.1).bitLaw (v:=v i.1) hD η κ n).map (bitReindex (flagSitePermutation hD i.2.val))) ε := by
    apply eventually_all.mpr
    intro i
    filter_upwards [ht i η hη hη₁ κ hκ δ d hδ hd] with n hn
    apply hn.mono
    have hi₁ : C₁ i≤A := Finset.single_le_sum (fun t _ => hC₁ t) (Finset.mem_univ i)
    have hi₂ : C₂ i≤B := Finset.single_le_sum (fun t _ => hC₂ t) (Finset.mem_univ i)
    have he : C₁ i*η+C₂ i*Real.sqrt κ+δ≤A*η+B*Real.sqrt κ+δ :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_right hi₁ hη.le)
        (mul_le_mul_of_nonneg_right hi₂ (Real.sqrt_nonneg κ))) le_rfl
    exact (hsmall d (C₁ i*η+C₂ i*Real.sqrt κ+δ) hd.le le_rfl (add_nonneg (add_nonneg (mul_nonneg (hC₁ i) hη.le)
      (mul_nonneg (hC₂ i) (Real.sqrt_nonneg κ))) hδ.le) he).le
  filter_upwards [hh] with n hn g hg j
  exact hn (j,⟨g,hg⟩)

theorem jointBitFieldLaw_transport {k a m D : ℕ} (v : Fin k → ℝ×ℝ)
    (S : Fin k → FieldSignalData) (hD : 0<D) (F : Finset (polygonFullGroup a m))
    {ε : ℝ} (hε : 0<ε) :
    ∃η κ : ℝ,0<η ∧ η≤1 ∧ 0<κ ∧ ∀ᶠn : ℕ in atTop,∀g∈F,
      ObservableClose (jointBitFieldLaw (a:=a) (m:=m) v S hD η κ n)
        ((jointBitFieldLaw (a:=a) (m:=m) v S hD η κ n).map (jointBitReindex v hD g)) ε := by
  have hk : (0:ℝ)<(k:ℝ)+1 := by positivity
  obtain ⟨η,κ,hη,hη₁,hκ,ht⟩ := finiteSignalFields_transport v S hD F (div_pos hε hk)
  refine ⟨η,κ,hη,hη₁,hκ,?_⟩
  filter_upwards [ht] with n hn g hg
  let μ (j : Fin k) := (S j).bitLaw (a:=a) (m:=m) (v:=v j) hD η κ n
  have (j : Fin k) : IsProbabilityMeasure ((μ j).map (bitReindex (flagSitePermutation hD g))) :=
    inferInstance
  have hh := ObservableClose.fin_pi k μ
    (fun j => (μ j).map (bitReindex (flagSitePermutation hD g)))
    (fun _ => ε/((k:ℝ)+1)) (fun j => hn g hg j)
  rw [← Measure.pi_map_pi (fun j => (bitReindex_measurable (flagSitePermutation (v:=v j) hD g)).aemeasurable)] at hh
  apply hh.mono
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  rw [← mul_div_assoc]
  exact (div_le_iff₀ hk).mpr (by nlinarith)

end JointBitField

section JointFieldSuccess
open Classical MeasureTheory Filter Set
open scoped Topology

noncomputable def jointFieldSuccess {k a m D : ℕ} (v : Fin k → ℝ×ℝ)
    (S : Fin k → FieldSignalData) (n : ℕ) (b : ∀j,FlagSite a m D (v j) → Bool) : Prop :=
  ∀j,signalSuccess (flagMeanSignal (S j).signal (sourceDyadicN n)) (b j)

theorem jointFieldSuccess_measurable {k a m D : ℕ} (v : Fin k → ℝ×ℝ)
    (S : Fin k → FieldSignalData) (n : ℕ) :
    MeasurableSet {b : ∀j,FlagSite a m D (v j) → Bool | jointFieldSuccess v S n b} := by
  simp only [jointFieldSuccess,Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro j
  exact (measurable_pi_apply (X:=fun j : Fin k => FlagSite a m D (v j) → Bool) j) (signalSuccess_measurable
    (flagMeanSignal (S j).signal (sourceDyadicN n) : FlagSite a m D (v j) → ℝ))

theorem jointBitFieldLaw_success {k a m D : ℕ} (v : Fin k → ℝ×ℝ)
    (S : Fin k → FieldSignalData) (hD : 0<D) {η κ : ℝ} (hη : 0<η) (hκ : 0<κ) :
    Tendsto (fun n => (jointBitFieldLaw (a:=a) (m:=m) v S hD η κ n).real
      {b | ¬jointFieldSuccess v S n b}) atTop (nhds 0) := by
  let μ (n : ℕ) (j : Fin k) := (S j).bitLaw (a:=a) (m:=m) (v:=v j) hD η κ n
  let E (n : ℕ) (j : Fin k) := {b : FlagSite a m D (v j) → Bool |
    ¬signalSuccess (flagMeanSignal (S j).signal (sourceDyadicN n)) b}
  have ht (j : Fin k) : Tendsto (fun n => (μ n j).real (E n j)) atTop (nhds 0) :=
    sourceBitFieldLaw_success hD (S j).signal (S j).χ (S j).χ_range (S j).L_pos (S j).χ_zero
      (by positivity) hη hκ
  have hs : Tendsto (fun n => ∑j,(μ n j).real (E n j)) atTop (nhds 0) := by
    simpa only [Finset.sum_const_zero] using tendsto_finsetSum Finset.univ (fun j _ => ht j)
  apply squeeze_zero (fun _ => measureReal_nonneg) _ hs
  intro n
  have he : {b : ∀j,FlagSite a m D (v j) → Bool | ¬jointFieldSuccess v S n b}=
      ⋃j,Function.eval j ⁻¹' E n j := by ext b; simp [jointFieldSuccess,E]
  rw [he]
  apply (measureReal_iUnion_fintype_le _).trans
  apply Finset.sum_le_sum
  intro j _
  have hp := measurePreserving_eval (μ n) j
  have hm : MeasurableSet (E n j) := (signalSuccess_measurable _).compl
  have hh := map_measureReal_apply (μ:=Measure.pi (μ n)) hp.measurable hm
  rw [hp.map_eq] at hh
  exact hh.symm.le

theorem jointBitFieldLaw_finite_support {k a m D : ℕ} (v : Fin k → ℝ×ℝ)
    (S : Fin k → FieldSignalData) (hq : ∀j,(S j).q=-3) (hD : 0<D)
    (η κ : ℝ) (n : ℕ) :
    ∃T : Finset (∀j,FlagSite a m D (v j) → Bool),
      ∀ᵐb ∂jointBitFieldLaw (a:=a) (m:=m) v S hD η κ n,b∈T := by
  let μ (j : Fin k) := (S j).bitLaw (a:=a) (m:=m) (v:=v j) hD η κ n
  have hc (j : Fin k) : ∀x,(S j).L≤‖x‖ → (S j).signal x=-3 := by
    intro x hx
    have hzero := (S j).ψ_zero x (by linarith [(S j).gap])
    simp only [FieldSignalData.signal,hzero,hq j,add_zero]
  choose T hT using (fun j => sourceBitFieldLaw_finite_support (a:=a) (m:=m) (v:=v j)
    hD (S j).signal (S j).χ (S j).L_pos (S j).χ_zero (hc j) ((D:ℝ)^4/5) η κ n)
  have hf : Set.Finite (Set.univ.pi (fun j => (T j : Set (FlagSite a m D (v j) → Bool)))) :=
    Set.Finite.pi (fun j => (T j).finite_toSet)
  refine ⟨hf.toFinset,?_⟩
  simp only [Set.Finite.mem_toFinset,Set.mem_pi,Set.mem_univ,true_implies,Finset.mem_coe]
  apply ae_all_iff.mpr
  intro j
  exact (measurePreserving_eval μ j).quasiMeasurePreserving.ae (hT j)

end JointFieldSuccess

end SimpleAmenable
end
end

end OAI
