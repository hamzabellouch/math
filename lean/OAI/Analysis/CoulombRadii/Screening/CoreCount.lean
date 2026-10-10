import Mathlib
import OAI.Analysis.CoulombRadii.RandomFields.RecordedEnsemble
import OAI.Analysis.CoulombRadii.ThomasFermi.BinaryEnsemble

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace Coulomb

lemma localCount_core_le {m k : ℕ} (A : Set Space) (x : Configuration (m+k))
    (hx : ∀ i : Fin k, position x (Fin.natAdd m i)∈A) : (k:ℝ)≤localCount A x := by
  unfold localCount
  rw [Fin.sum_univ_add]
  have he : (∑ i : Fin k, A.indicator (fun _ => (1:ℝ)) (position x (Fin.natAdd m i)))=k := by
    simp only [indicator_of_mem (hx _),Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
  rw [he]
  exact le_add_of_nonneg_left (Finset.sum_nonneg (fun _ _ => indicator_nonneg (fun _ _ => zero_le_one) _))

lemma localCount_le_core {m k : ℕ} (A : Set Space) (x : Configuration (m+k))
    (hx : ∀ i : Fin m, position x (Fin.castAdd k i)∉A) : localCount A x≤(k:ℝ) := by
  unfold localCount
  rw [Fin.sum_univ_add]
  have he : (∑ i : Fin m, A.indicator (fun _ => (1:ℝ)) (position x (Fin.castAdd k i)))=0 := by
    simp only [indicator_of_notMem (hx _),Finset.sum_const_zero]
  rw [he,zero_add]
  calc
    _ ≤ ∑ _i : Fin k, (1:ℝ) := Finset.sum_le_sum (fun i _ => by
      by_cases h : position x (Fin.natAdd m i)∈A <;> simp [h])
    _ = _ := by simp

lemma PartlySupported.core_population {m k : ℕ} {v : H1Vector (m+k)}
    {A : Set Space} (hA : MeasurableSet A) (hv : PartlySupported v (coreIndexSet m k) A) :
    (k:ℝ)*mass v≤expectedPopulation v A := by
  rw [expectedPopulation_eq v hA]
  unfold mass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s hs
  rw [←integral_const_mul]
  apply integral_mono_ae (((v.value_L2 s).integrable_norm_pow (p:=2) (by norm_num)).const_mul _)
    (by simpa using localCount_weight_integrable v hA s 1)
  filter_upwards [hv s] with x hx
  by_cases hz : v.value s x=0
  · simp [hz]
  · apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact localCount_core_le A x (fun i => by
      by_contra h
      exact hz (hx _ ⟨i,rfl⟩ h))

def positiveInnerDeficit {n : ℕ} (Z : ℝ) (A : Set Space) (x : Configuration n) : ℝ :=
  max (Z-localCount A x) 0

lemma positiveInnerDeficit_measurable {n : ℕ} (Z : ℝ) {A : Set Space} (hA : MeasurableSet A) :
    Measurable (positiveInnerDeficit (n:=n) Z A) :=
  (measurable_const.sub (localCount_measurable hA)).max measurable_const

lemma positiveInnerDeficit_nonneg {n : ℕ} (Z : ℝ) (A : Set Space) (x : Configuration n) :
    0≤positiveInnerDeficit Z A x := le_max_right _ _

lemma positiveInnerDeficit_le {n : ℕ} {Z : ℝ} (hZ : 0≤Z) (A : Set Space) (x : Configuration n) :
    positiveInnerDeficit Z A x≤Z := max_le (sub_le_self _ (localCount_nonneg _ _)) hZ

lemma PartlySupported.deficit_moment {m k : ℕ} {v : H1Vector (m+k)} {Z : ℝ} (hZ : 0≤Z)
    {A B : Set Space} (hA : MeasurableSet A) (hAB : Disjoint A B)
    (hv : PartlySupported v (outIndexSet m k) B) :
    (max (Z-(k:ℝ)) 0)^2*mass v≤potentialForm (fun x => (positiveInnerDeficit Z A x)^2) v := by
  unfold mass potentialForm
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s hs
  rw [←integral_const_mul]
  apply integral_mono_ae (((v.value_L2 s).integrable_norm_pow (p:=2) (by norm_num)).const_mul _)
    (boundedObservable_integrable v _ ((positiveInnerDeficit_measurable Z hA).pow_const 2)
      (fun x => by
        rw [abs_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (positiveInnerDeficit_nonneg _ _ _) (positiveInnerDeficit_le hZ A x) 2) s)
  filter_upwards [hv s] with x hx
  by_cases hz : v.value s x=0
  · simp [hz]
  · apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    apply pow_le_pow_left₀ (le_max_right _ _)
    apply max_le_max_right
    apply sub_le_sub_left
    exact localCount_le_core A x (fun i hi => by
      have hn : position x (Fin.castAdd k i)∉B := fun h => Set.disjoint_left.mp hAB hi h
      exact hz (hx _ ⟨i,rfl⟩ hn))

namespace RecordedEnsemble

def coreMean {n : ℕ} (T : RecordedEnsemble n) : ℝ := ∑ p, (T.core p:ℝ)*mass (T.vector p)
def coreDeficitMoment {n : ℕ} (T : RecordedEnsemble n) (Z : ℝ) : ℝ :=
  ∑ p, (max (Z-(T.core p:ℝ)) 0)^2*mass (T.vector p)
def favorableMass {n : ℕ} (T : RecordedEnsemble n) (Z : ℝ) : ℝ :=
  ∑ p, if (T.core p:ℝ)<Z then mass (T.vector p) else 0

lemma coreMean_le_population {n : ℕ} {T : RecordedEnsemble n} {ψ : H1Vector n}
    (hT : T.Conserves ψ) {A : Set Space} (hA : MeasurableSet A) (hs : T.CoreSupported A) :
    T.coreMean≤expectedPopulation ψ A := by
  rw [←hT.population hA]
  exact Finset.sum_le_sum (fun p _ => (hs p).core_population hA)

lemma coreDeficitMoment_le_raw {n : ℕ} {T : RecordedEnsemble n} {ψ : H1Vector n}
    (hT : T.Conserves ψ) {Z : ℝ} (hZ : 0≤Z) {A B : Set Space} (hA : MeasurableSet A)
    (hAB : Disjoint A B) (hs : T.OutSupported B) :
    T.coreDeficitMoment Z≤potentialForm (fun x => (positiveInnerDeficit Z A x)^2) ψ := by
  have H := hT (fun x => (positiveInnerDeficit Z A x)^2)
    ((positiveInnerDeficit_measurable Z hA).pow_const 2)
    ⟨Z^2,fun x => by rw [abs_of_nonneg (sq_nonneg _)]; exact
      pow_le_pow_left₀ (positiveInnerDeficit_nonneg _ _ _) (positiveInnerDeficit_le hZ A x) 2⟩
  have he p : (fun x => (positiveInnerDeficit (n:=n) Z A x)^2) ∘ reindexConfiguration (T.labels p)=
      (fun x => (positiveInnerDeficit Z A x)^2) := by
    funext x
    simp only [Function.comp_def,positiveInnerDeficit,localCount_reindex]
  simp only [he] at H
  rw [←H]
  exact Finset.sum_le_sum (fun p _ => (hs p).deficit_moment hZ hA hAB)

lemma favorableMass_of_core_moments {n : ℕ} (T : RecordedEnsemble n) {Z M : ℝ}
    (hM : 0<M) (hm : T.totalMass=1) (hmean : 1≤Z-T.coreMean) (hsecond : T.coreDeficitMoment Z≤M) :
    1/M≤T.favorableMass Z := by
  have H p : 2*M*(Z-(T.core p:ℝ))*mass (T.vector p)≤
      (max (Z-(T.core p:ℝ)) 0)^2*mass (T.vector p)+
      M^2*(if (T.core p:ℝ)<Z then mass (T.vector p) else 0) := by
    by_cases hp : (T.core p:ℝ)<Z
    · rw [ite_eq_left hp,max_eq_left (by linarith)]
      nlinarith [mul_nonneg (sq_nonneg (Z-(T.core p:ℝ)-M)) (mass_nonneg (T.vector p))]
    · rw [ite_eq_right hp,max_eq_right (by linarith)]
      simp only [zero_pow (by decide : 2≠0),zero_mul,mul_zero,add_zero]
      exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)) (mass_nonneg _)
  have HH := Finset.sum_le_sum (s:=Finset.univ) (fun p _ => H p)
  have he : (∑ p, 2*M*(Z-(T.core p:ℝ))*mass (T.vector p))=2*M*(Z*T.totalMass-T.coreMean) := by
    simp only [totalMass,coreMean,Finset.mul_sum,Finset.sum_sub_distrib,mul_sub,sub_mul]
    simp only [mul_assoc]
  rw [he,hm,mul_one] at HH
  simp only [Finset.sum_add_distrib,←Finset.mul_sum] at HH
  change 2*M*(Z-T.coreMean)≤T.coreDeficitMoment Z+M^2*T.favorableMass Z at HH
  apply (div_le_iff₀ hM).mpr
  apply (mul_le_mul_iff_left₀ hM).mp
  nlinarith [mul_le_mul_of_nonneg_left hmean (show 0≤2*M by positivity)]

end RecordedEnsemble
end Coulomb
end

end

end OAI
