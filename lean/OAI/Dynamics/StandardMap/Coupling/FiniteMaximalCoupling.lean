import OAI.Dynamics.StandardMap.EntropyEndpoint
import OAI.Dynamics.StandardMap.Bernoulli.IntegerDynamics

namespace OAI

section
section
namespace HyperbolicCoding
open MeasureTheory Set
open scoped BigOperators ENNReal

theorem finite_maximal_coupling_equal_mass {A : Type*} [Fintype A] [DecidableEq A]
    (p q : A → ℝ) (hp : ∀ a,0≤p a) (hq : ∀ a,0≤q a)
    (heq : ∑ a,p a=∑ a,q a) :
    ∃ r : A → A → ℝ,(∀ a b,0≤r a b) ∧
      (∀ a,∑ b,r a b=p a) ∧ (∀ b,∑ a,r a b=q b) ∧
      (∑ a,∑ b,r a b*(if a=b then 0 else 1))=∑ a,max (p a-q a) 0 := by
  classical
  let d : A → ℝ := fun a => min (p a) (q a)
  let u : A → ℝ := fun a => p a-d a
  let v : A → ℝ := fun a => q a-d a
  let t : ℝ := ∑ a,u a
  have hd (a) : 0≤d a := le_min (hp a) (hq a)
  have hu (a) : 0≤u a := sub_nonneg.mpr (min_le_left _ _)
  have hv (a) : 0≤v a := sub_nonneg.mpr (min_le_right _ _)
  have ht : 0≤t := Finset.sum_nonneg (fun a _ => hu a)
  have htv : ∑ a,v a=t := by
    dsimp only [t,u,v]
    rw [Finset.sum_sub_distrib,Finset.sum_sub_distrib,heq]
  have huv (a) : u a*v a=0 := by
    rcases le_total (p a) (q a) with ha | ha
    · simp only [u,v,d,min_eq_left ha,sub_self,zero_mul]
    · simp only [u,v,d,min_eq_right ha,sub_self,mul_zero]
  have hmax (a) : u a=max (p a-q a) 0 := by
    rcases le_total (p a) (q a) with ha | ha
    · simp only [u,d,min_eq_left ha,sub_self,max_eq_right (sub_nonpos.mpr ha)]
    · simp only [u,d,min_eq_right ha,max_eq_left (sub_nonneg.mpr ha)]
  by_cases ht0 : t=0
  · have hu0 (a) : u a=0 := by
      have hh := Finset.single_le_sum (fun b _ => hu b) (Finset.mem_univ a)
      change u a≤t at hh
      rw [ht0] at hh
      exact le_antisymm hh (hu a)
    have hv0 (a) : v a=0 := by
      have hh := Finset.single_le_sum (fun b _ => hv b) (Finset.mem_univ a)
      rw [htv,ht0] at hh
      exact le_antisymm hh (hv a)
    refine ⟨fun a b => if a=b then p a else 0,?_,?_,?_,?_⟩
    · intro a b
      dsimp only
      split_ifs
      · exact hp a
      · exact le_rfl
    · intro a; simp
    · intro b
      simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
      have h1 := hu0 b
      have h2 := hv0 b
      dsimp [u,v] at h1 h2
      linarith
    · have he (a b : A) : (if a=b then p a else 0)*(if a=b then (0 : ℝ) else 1)=0 := by
        by_cases h : a=b <;> simp [h]
      simp_rw [he]
      simp only [Finset.sum_const_zero]
      rw [←show (∑ a,u a)=(∑ a,max (p a-q a) 0) from Finset.sum_congr rfl (fun a _ => hmax a)]
      exact ht0.symm
  · have htpos : 0<t := lt_of_le_of_ne ht (Ne.symm ht0)
    let r : A → A → ℝ := fun a b => (if a=b then d a else 0)+u a*v b/t
    have hr (a b) : 0≤r a b := by
      dsimp only [r]
      exact add_nonneg (by split_ifs; exact hd a; exact le_rfl) (div_nonneg (mul_nonneg (hu a) (hv b)) ht)
    have hrow (a) : ∑ b,r a b=p a := by
      simp only [r,Finset.sum_add_distrib,Finset.sum_ite_eq,Finset.mem_univ,ite_true,
        ←Finset.sum_div,←Finset.mul_sum,htv,mul_div_cancel_right₀ _ ht0]
      dsimp only [u]
      ring
    have hcol (b) : ∑ a,r a b=q b := by
      simp only [r,Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,ite_true,
        ←Finset.sum_div,←Finset.sum_mul]
      change d b+t*v b/t=q b
      rw [mul_div_cancel_left₀ _ ht0]
      dsimp only [v]
      ring
    refine ⟨r,hr,hrow,hcol,?_⟩
    have hoff (a b) : r a b*(if a=b then 0 else 1)=u a*v b/t := by
      by_cases hab : a=b
      · subst b; simp [huv]
      · simp only [r,ite_eq_right hab,zero_add,mul_one]
    simp_rw [hoff]
    simp only [←Finset.sum_div,←Finset.mul_sum,htv,mul_div_cancel_right₀ _ ht0]
    exact Finset.sum_congr rfl (fun a _ => hmax a)

theorem finite_maximal_coupling {A : Type*} [Fintype A] [DecidableEq A]
    (p q : A → ℝ) (hp : ∀ a,0≤p a) (hq : ∀ a,0≤q a)
    (hp1 : ∑ a,p a=1) (hq1 : ∑ a,q a=1) :
    ∃ r : A → A → ℝ,(∀ a b,0≤r a b) ∧
      (∀ a,∑ b,r a b=p a) ∧ (∀ b,∑ a,r a b=q b) ∧
      (∑ a,∑ b,r a b*(if a=b then 0 else 1))=∑ a,max (p a-q a) 0 :=
  finite_maximal_coupling_equal_mass p q hp hq (hp1.trans hq1.symm)

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set
open scoped BigOperators ENNReal

lemma positive_mass_difference_le {A : Type*} [Fintype A] [MeasurableSpace A]
    [MeasurableSingletonClass A] (μ ν : Measure A) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {ε : ℝ} (h : LawClose μ ν ε) :
    (∑ a,max (μ.real {a}-ν.real {a}) 0)≤ε := by
  classical
  let D := Finset.univ.filter (fun a : A => ν.real {a}≤μ.real {a})
  have hm (a : A) : max (μ.real {a}-ν.real {a}) 0=
      if ν.real {a}≤μ.real {a} then μ.real {a}-ν.real {a} else 0 := by
    split_ifs with ha
    · exact max_eq_left (sub_nonneg.mpr ha)
    · exact max_eq_right (sub_nonpos.mpr (le_of_not_ge ha))
  have he : (∑ a,max (μ.real {a}-ν.real {a}) 0)=μ.real D-ν.real D := by
    simp_rw [hm]
    rw [←Finset.sum_filter]
    change (∑ a∈D,(μ.real {a}-ν.real {a}))=_
    rw [Finset.sum_sub_distrib,sum_measureReal_singleton,sum_measureReal_singleton]
  rw [he]
  exact (le_abs_self _).trans (h D D.measurableSet)

theorem finite_coupling_of_lawClose {A : Type*} [Fintype A] [DecidableEq A]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (μ ν : Measure A) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {ε : ℝ} (h : LawClose μ ν ε) :
    ∃ r : A → A → ℝ,(∀ a b,0≤r a b) ∧
      (∀ a,∑ b,r a b=μ.real {a}) ∧ (∀ b,∑ a,r a b=ν.real {b}) ∧
      (∑ a,∑ b,r a b*(if a=b then 0 else 1))≤ε := by
  obtain ⟨r,hr,hrow,hcol,herr⟩ := finite_maximal_coupling (fun a => μ.real {a}) (fun a => ν.real {a})
    (fun _ => measureReal_nonneg) (fun _ => measureReal_nonneg)
    (by simp)
    (by simp)
  exact ⟨r,hr,hrow,hcol,herr.le.trans (positive_mass_difference_le μ ν h)⟩

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open scoped BigOperators
variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]

structure MatrixCoupling (p : A → ℝ) (q : B → ℝ) where
  weight : A → B → ℝ
  nonneg : ∀ a b,0≤weight a b
  row : ∀ a,∑ b,weight a b=p a
  col : ∀ b,∑ a,weight a b=q b

namespace MatrixCoupling
variable {p : A → ℝ} {q : B → ℝ} {s : C → ℝ}

lemma left_nonneg (r : MatrixCoupling p q) (a : A) : 0≤p a := by
  rw [←r.row a]
  exact Finset.sum_nonneg (fun b _ => r.nonneg a b)
lemma right_nonneg (r : MatrixCoupling p q) (b : B) : 0≤q b := by
  rw [←r.col b]
  exact Finset.sum_nonneg (fun a _ => r.nonneg a b)
lemma le_left (r : MatrixCoupling p q) (a : A) (b : B) : r.weight a b≤p a := by
  rw [←r.row a]
  exact Finset.single_le_sum (fun b _ => r.nonneg a b) (Finset.mem_univ b)
lemma le_right (r : MatrixCoupling p q) (a : A) (b : B) : r.weight a b≤q b := by
  rw [←r.col b]
  exact Finset.single_le_sum (fun a _ => r.nonneg a b) (Finset.mem_univ a)

noncomputable def glueWeight (r : MatrixCoupling p q) (t : MatrixCoupling q s)
    (a : A) (b : B) (c : C) : ℝ := r.weight a b*t.weight b c/q b

lemma glueWeight_nonneg (r : MatrixCoupling p q) (t : MatrixCoupling q s) (a b c) :
    0≤glueWeight r t a b c := div_nonneg (mul_nonneg (r.nonneg _ _) (t.nonneg _ _)) (r.right_nonneg b)

lemma glueWeight_row (r : MatrixCoupling p q) (t : MatrixCoupling q s) (a b) :
    (∑ c,glueWeight r t a b c)=r.weight a b := by
  simp only [glueWeight,←Finset.sum_div,←Finset.mul_sum,t.row]
  by_cases hq : q b=0
  · have hz : r.weight a b=0 := le_antisymm (by simpa only [hq] using r.le_right a b) (r.nonneg a b)
    simp [hq,hz]
  · exact mul_div_cancel_right₀ _ hq

lemma glueWeight_col (r : MatrixCoupling p q) (t : MatrixCoupling q s) (b c) :
    (∑ a,glueWeight r t a b c)=t.weight b c := by
  simp only [glueWeight,←Finset.sum_div,←Finset.sum_mul,r.col]
  by_cases hq : q b=0
  · have hz : t.weight b c=0 := le_antisymm (by simpa only [hq] using t.le_left b c) (t.nonneg b c)
    simp [hq,hz]
  · exact mul_div_cancel_left₀ _ hq

noncomputable def comp (r : MatrixCoupling p q) (t : MatrixCoupling q s) : MatrixCoupling p s where
  weight a c := ∑ b,glueWeight r t a b c
  nonneg a c := Finset.sum_nonneg (fun b _ => glueWeight_nonneg r t a b c)
  row a := by rw [Finset.sum_comm]; simp only [glueWeight_row,r.row]
  col c := by rw [Finset.sum_comm]; simp only [glueWeight_col,t.col]

noncomputable def cost (r : MatrixCoupling p q) (d : A → B → ℝ) := ∑ a,∑ b,r.weight a b*d a b

lemma comp_cost_le (r : MatrixCoupling p q) (t : MatrixCoupling q s)
    (d : A → B → ℝ) (e : B → C → ℝ) (f : A → C → ℝ)
    (htri : ∀ a b c,f a c≤d a b+e b c) :
    (r.comp t).cost f≤r.cost d+t.cost e := by
  unfold cost comp
  simp only [Finset.sum_mul]
  calc
    _≤∑ a,∑ c,∑ b,glueWeight r t a b c*(d a b+e b c) :=
      Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun c _ =>
        Finset.sum_le_sum (fun b _ => mul_le_mul_of_nonneg_left (htri a b c) (glueWeight_nonneg r t a b c))))
    _=(∑ a,∑ c,∑ b,glueWeight r t a b c*d a b)+
        (∑ a,∑ c,∑ b,glueWeight r t a b c*e b c) := by
      simp only [mul_add,Finset.sum_add_distrib]
    _=(∑ a,∑ b,r.weight a b*d a b)+(∑ b,∑ c,t.weight b c*e b c) := by
      congr 1
      · apply Finset.sum_congr rfl
        intro a _
        rw [Finset.sum_comm]
        simp only [←Finset.sum_mul,glueWeight_row]
      · rw [Finset.sum_comm]
        calc
          _ = ∑ c,∑ b,∑ a,glueWeight r t a b c*e b c := by
            apply Finset.sum_congr rfl
            intro c _
            exact Finset.sum_comm
          _ = ∑ c,∑ b,t.weight b c*e b c := by simp only [←Finset.sum_mul,glueWeight_col]
          _ = _ := Finset.sum_comm

end MatrixCoupling
end HyperbolicCoding

end
section
namespace StandardMapEntropy.Entropy
open MeasureTheory Set Filter
open scoped ENNReal Topology BigOperators
variable {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]
    [Fintype A] [MeasurableSingletonClass A]

lemma integrable_finite_observation (μ : Measure X) [IsFiniteMeasure μ]
    (p : X → A) (hp : Measurable p) (g : A → ℝ) : Integrable (fun x => g (p x)) μ := by
  classical
  apply Integrable.of_bound ((measurable_of_countable g).comp hp).aestronglyMeasurable (∑ a,|g a|)
  exact ae_of_all _ (fun x => by
    rw [Real.norm_eq_abs]
    exact Finset.single_le_sum (fun a _ => abs_nonneg (g a)) (Finset.mem_univ _))

noncomputable def information (μ : Measure X) (p : X → A) (x : X) : ℝ :=
  -Real.log (mass μ p (p x))

lemma information_measurable (μ : Measure X) (p : X → A) (hp : Measurable p) :
    Measurable (information μ p) := (measurable_of_countable (fun a : A => -Real.log (mass μ p a))).comp hp

lemma information_integrable (μ : Measure X) [IsFiniteMeasure μ]
    (p : X → A) (hp : Measurable p) : Integrable (information μ p) μ :=
  integrable_finite_observation μ p hp (fun a : A => -Real.log (mass μ p a))

lemma integral_information (μ : Measure X) [IsFiniteMeasure μ]
    (p : X → A) (hp : Measurable p) : (∫ x,information μ p x ∂μ)=obs μ p := by
  simp only [information]
  rw [←sum_mass_mul_integral μ p hp (fun a => -Real.log (mass μ p a))]
  simp only [obs,shannon,Real.negMulLog,mul_neg,neg_mul]

lemma information_nonneg (μ : Measure X) [IsProbabilityMeasure μ]
    (p : X → A) (hp : Measurable p) (x : X) : 0 ≤ information μ p x :=
  neg_nonneg.mpr (Real.log_nonpos (mass_nonneg μ p _) (mass_le_one μ p hp _))

omit [MeasurableSpace A] [MeasurableSingletonClass A] in
lemma ae_mass_positive (μ : Measure X) [IsFiniteMeasure μ] (p : X → A) :
    ∀ᵐ x ∂μ,0 < mass μ p (p x) := by
  have hzero (a : A) : ∀ᵐ x ∂μ,mass μ p a=0 → p x≠a := by
    by_cases ha : mass μ p a=0
    · have hm : μ (p ⁻¹' {a})=0 := by
        apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ _) ENNReal.zero_ne_top).mp
        exact ha
      filter_upwards [measure_eq_zero_iff_ae_notMem.mp hm] with x hx _h
      exact hx
    · exact ae_of_all _ (fun _ h => (ha h).elim)
  filter_upwards [ae_all_iff.mpr hzero] with x hx
  exact lt_of_le_of_ne (mass_nonneg μ p _) (Ne.symm (fun h => hx (p x) h rfl))

lemma weighted_positive_log_ratio_le {u v : ℝ} (hu : 0≤u) (hv : 0≤v)
    (hs : u≠0 → v≠0) : u*max (Real.log v-Real.log u) 0≤v := by
  by_cases hu0 : u=0
  · simp only [hu0,zero_mul]; exact hv
  have hu' : 0<u := lt_of_le_of_ne hu (Ne.symm hu0)
  have hv' : 0<v := lt_of_le_of_ne hv (Ne.symm (hs hu0))
  by_cases hlog : 0≤Real.log v-Real.log u
  · rw [max_eq_left hlog]
    have hh := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos hv' hu')) hu
    rw [Real.log_div hv'.ne' hu'.ne'] at hh
    have he : u*(v/u-1)=v-u := by field_simp
    rw [he] at hh
    linarith
  · rw [max_eq_right (le_of_not_ge hlog),mul_zero]
    exact hv

theorem information_reference_excess (μ : Measure X) [IsProbabilityMeasure μ]
    (p : X → A) (hp : Measurable p) (q : A → ℝ) (hq : ∀ a,0≤q a)
    (hs : ∀ a,mass μ p a≠0 → q a≠0) (hm : ∑ a,q a≤1) :
    (∫ x,max (information μ p x-(-Real.log (q (p x)))) 0 ∂μ)≤1 := by
  simp only [information]
  rw [←sum_mass_mul_integral μ p hp (fun a => max (-Real.log (mass μ p a)-(-Real.log (q a))) 0)]
  apply le_trans (Finset.sum_le_sum (fun a _ => ?_)) hm
  rw [show -Real.log (mass μ p a)-(-Real.log (q a))=Real.log (q a)-Real.log (mass μ p a) from by ring]
  exact weighted_positive_log_ratio_le (mass_nonneg μ p a) (hq a) (hs a)

end StandardMapEntropy.Entropy

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped ENNReal BigOperators
variable {X A B C D : Type*} [MeasurableSpace X]
    [Fintype A] [Fintype B] [Fintype C] [Fintype D]

namespace MatrixCoupling
variable {p : A → ℝ} {q : B → ℝ} {s : C → ℝ} {t : D → ℝ}

noncomputable def symm (r : MatrixCoupling p q) : MatrixCoupling q p where
  weight b a := r.weight a b
  nonneg b a := r.nonneg a b
  row b := r.col b
  col a := r.row a

noncomputable def diagonal (p : A → ℝ) (hp : ∀ a,0≤p a) : MatrixCoupling p p := by
  classical
  exact {
    weight := fun a b => if a=b then p a else 0
    nonneg := fun a b => by split_ifs; exact hp a; exact le_rfl
    row := fun a => by simp
    col := fun b => by simp }

lemma diagonal_cost (p : A → ℝ) (hp : ∀ a,0≤p a) (d : A → A → ℝ)
    (hd : ∀ a,d a a=0) : (diagonal p hp).cost d=0 := by
  classical
  unfold cost diagonal
  simp only [ite_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,ite_true,hd,mul_zero,Finset.sum_const_zero]

noncomputable def product (r : MatrixCoupling p q) (u : MatrixCoupling s t) :
    MatrixCoupling (fun ac : A×C => p ac.1*s ac.2) (fun bd : B×D => q bd.1*t bd.2) where
  weight ac bd := r.weight ac.1 bd.1*u.weight ac.2 bd.2
  nonneg ac bd := mul_nonneg (r.nonneg _ _) (u.nonneg _ _)
  row ac := by simp only [Fintype.sum_prod_type,←Finset.mul_sum,←Finset.sum_mul,r.row,u.row]
  col bd := by simp only [Fintype.sum_prod_type,←Finset.mul_sum,←Finset.sum_mul,r.col,u.col]

lemma product_cost (r : MatrixCoupling p q) (u : MatrixCoupling s t)
    (hp : ∑ a,p a=1) (hs : ∑ c,s c=1) (d : A → B → ℝ) (e : C → D → ℝ) :
    (r.product u).cost (fun ac bd => d ac.1 bd.1+e ac.2 bd.2)=r.cost d+u.cost e := by
  unfold cost product
  simp only [Fintype.sum_prod_type,mul_add,Finset.sum_add_distrib]
  congr 1
  · calc
      _ = ∑ a,∑ c,∑ b,r.weight a b*d a b*(∑ v,u.weight c v) := by
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro c _
        apply Finset.sum_congr rfl
        intro b _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro v _
        ring
      _ = ∑ a,∑ c,∑ b,r.weight a b*d a b*s c := by simp only [u.row]
      _ = ∑ a,∑ b,r.weight a b*d a b := by
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.sum_comm]
        simp only [←Finset.mul_sum,hs,mul_one]
  · calc
      _ = ∑ a,∑ c,(∑ b,r.weight a b)*(∑ v,u.weight c v*e c v) := by
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro c _
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro b _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro v _
        ring
      _ = ∑ a,∑ c,p a*(∑ v,u.weight c v*e c v) := by simp only [r.row]
      _ = ∑ c,∑ v,u.weight c v*e c v := by
        rw [Finset.sum_comm]
        simp only [←Finset.sum_mul,hp,one_mul]

section Observations
variable [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [MeasurableSingletonClass B]
variable (μ : Measure X) [IsFiniteMeasure μ]

noncomputable def observations (p : X → A) (q : X → B) (hp : Measurable p) (hq : Measurable q) :
    MatrixCoupling (mass μ p) (mass μ q) where
  weight a b := mass μ (fun x => (p x,q x)) (a,b)
  nonneg _ _ := mass_nonneg _ _ _
  row a := (mass_joint_row μ p q hp hq a).symm
  col b := (mass_joint_col μ p q hp hq b).symm

lemma observations_cost (p : X → A) (q : X → B) (hp : Measurable p) (hq : Measurable q)
    (d : A → B → ℝ) : (observations μ p q hp hq).cost d=∫ x,d (p x) (q x) ∂μ := by
  change (∑ a,∑ b,mass μ (fun x => (p x,q x)) (a,b)*d a b)=_
  simpa only [Fintype.sum_prod_type] using
    sum_mass_mul_integral μ (fun x => (p x,q x)) (hp.prodMk hq) (fun ab => d ab.1 ab.2)

end Observations
end MatrixCoupling
end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set Filter
open scoped ENNReal Topology

lemma continuous_cdf_atomless (ν : Measure ℝ) [IsProbabilityMeasure ν]
    [NullSingletonClass ν] : Continuous (cdf ν) := by
  have hc : Continuous (fun a : ℝ => ∫ _x in Iic a,(1 : ℝ) ∂ν) := by
    rw [continuous_iff_continuousAt]
    intro a
    have h := ((integrable_const (1 : ℝ)).integrableOn : IntegrableOn (fun _x : ℝ => (1 : ℝ)) (Iic (a+1)) ν)
    exact (h.continuousOn_Iic_primitive_Iic a (by simp)).continuousAt (Iic_mem_nhds (by linarith))
  simpa only [integral_const,smul_eq_mul,mul_one,measureReal_restrict_apply_univ,←cdf_eq_real] using hc

theorem exists_event_real_mass {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] [NullSingletonClass μ]
    {t : ℝ} (ht : 0≤t) (ht1 : t≤1) :
    ∃ E : Set X,MeasurableSet E ∧ μ.real E=t := by
  by_cases ht0 : t=0
  · exact ⟨∅,MeasurableSet.empty,by simp [ht0]⟩
  by_cases hte : t=1
  · exact ⟨univ,MeasurableSet.univ,by simp [hte]⟩
  let b : X → ℝ := embeddingReal X
  have hb : MeasurableEmbedding b := measurableEmbedding_embeddingReal X
  let ν := μ.map b
  have : IsProbabilityMeasure ν := inferInstance
  have : NullSingletonClass ν := by
    constructor
    intro y
    rw [show ν=μ.map b from rfl,Measure.map_apply hb.measurable (measurableSet_singleton y)]
    by_cases hy : ∃ x,b x=y
    · obtain ⟨x,rfl⟩ := hy
      have hs : b ⁻¹' {b x}={x} := by
        ext z
        exact hb.injective.eq_iff
      simp only [hs,measure_singleton]
    · have hs : b ⁻¹' {y}=∅ := eq_empty_iff_forall_notMem.mpr (fun x hx => hy ⟨x,hx⟩)
      simp only [hs,measure_empty]
  have hs := isPreconnected_univ.intermediate_value_Ioo (s:=Set.univ)
    (show (atBot : Filter ℝ)≤𝓟 Set.univ by simp) (show (atTop : Filter ℝ)≤𝓟 Set.univ by simp)
    (continuous_cdf_atomless ν).continuousOn (tendsto_cdf_atBot ν) (tendsto_cdf_atTop ν)
    (show t∈Ioo (0 : ℝ) 1 from ⟨lt_of_le_of_ne ht (Ne.symm ht0),lt_of_le_of_ne ht1 hte⟩)
  obtain ⟨r,_hr,hrt⟩ := hs
  refine ⟨b ⁻¹' Iic r,measurableSet_Iic.preimage hb.measurable,?_⟩
  rw [←map_measureReal_apply hb.measurable measurableSet_Iic]
  exact (cdf_eq_real ν r).symm.trans hrt

theorem exists_subset_real_mass {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] [NullSingletonClass μ]
    {S : Set X} (hS : MeasurableSet S) {t : ℝ} (ht : 0≤t) (htS : t≤μ.real S) :
    ∃ E : Set X,MeasurableSet E ∧ E⊆S ∧ μ.real E=t := by
  by_cases ht0 : t=0
  · exact ⟨∅,MeasurableSet.empty,empty_subset _,by simp [ht0]⟩
  have htpos : 0<t := lt_of_le_of_ne ht (Ne.symm ht0)
  have hSr : 0<μ.real S := htpos.trans_le htS
  have hS0 : μ S≠0 := by
    intro h
    simp only [Measure.real,h,ENNReal.toReal_zero] at hSr
    exact lt_irrefl _ hSr
  let ν : Measure X := (μ S)⁻¹ • μ.restrict S
  have : IsProbabilityMeasure ν := by
    constructor
    simp only [ν,Measure.smul_apply,smul_eq_mul,Measure.restrict_apply MeasurableSet.univ,univ_inter]
    exact ENNReal.inv_mul_cancel hS0 (measure_ne_top μ S)
  have : NullSingletonClass ν := by
    constructor
    intro x
    have hz : μ ({x}∩S)=0 := measure_mono_null inter_subset_left (measure_singleton x)
    simp only [ν,Measure.smul_apply,smul_eq_mul,Measure.restrict_apply (measurableSet_singleton x),hz,mul_zero]
  obtain ⟨T,hT,hTm⟩ := exists_event_real_mass ν (div_nonneg ht hSr.le) ((div_le_one hSr).mpr htS)
  refine ⟨S∩T,hS.inter hT,inter_subset_left,?_⟩
  have he : ν.real T=μ.real (S∩T)/μ.real S := by
    simp only [ν,Measure.real,Measure.smul_apply,smul_eq_mul,Measure.restrict_apply hT,
      ENNReal.toReal_mul,ENNReal.toReal_inv,inter_comm T S,div_eq_mul_inv]
    ring
  rw [he] at hTm
  exact (div_left_inj' hSr.ne').mp hTm

end HyperbolicCoding

end
end

end OAI
