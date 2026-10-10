import OAI.Algebra.FormalGroup.Honda.Cocycle
import OAI.Algebra.FormalGroup.Honda.Canonical

namespace OAI

noncomputable section

namespace HeightThree.HondaJets
open MvPowerSeries
variable {K σ τ : Type*} [CommRing K]

def EqJet (n : ℕ) (f g : MvPowerSeries σ K) : Prop :=
  ∀ d, d.degree < n → coeff d f = coeff d g

lemma eqJet_iff_order (n : ℕ) (f g : MvPowerSeries σ K) :
    EqJet n f g ↔ (n : ℕ∞) ≤ (f-g).order := by
  constructor
  · intro h; apply nat_le_order; intro d hd; rw [map_sub,h d hd,sub_self]
  · intro h d hd
    have hh := coeff_of_lt_order ((show (d.degree : ℕ∞) < n by exact_mod_cast hd).trans_le h)
    exact sub_eq_zero.mp (by simpa using hh)

lemma eqJet_iff_trunc [Finite σ] (n : ℕ) (f g : MvPowerSeries σ K) :
    EqJet n f g ↔ f.truncTotal n = g.truncTotal n := by
  constructor
  · intro h; ext d
    by_cases hd : d.degree<n
    · simpa only [coeff_truncTotal _ hd] using h d hd
    · simp only [coeff_truncTotal_eq_zero _ (Nat.le_of_not_lt hd)]
  · intro h d hd
    simpa only [coeff_truncTotal _ hd] using congrArg (fun polynomial : MvPolynomial σ K => polynomial.coeff d) h

lemma EqJet.refl (n : ℕ) (f : MvPowerSeries σ K) : EqJet n f f := fun _ _ => rfl
lemma EqJet.symm {n : ℕ} {f g : MvPowerSeries σ K} (h : EqJet n f g) : EqJet n g f :=
  fun d hd => (h d hd).symm
lemma EqJet.trans {n : ℕ} {f g h : MvPowerSeries σ K} (h₁ : EqJet n f g)
    (h₂ : EqJet n g h) : EqJet n f h := fun d hd => (h₁ d hd).trans (h₂ d hd)
lemma EqJet.mono {n m : ℕ} {f g : MvPowerSeries σ K} (h : EqJet n f g) (hm : m≤n) :
    EqJet m f g := fun d hd => h d (hd.trans_le hm)
lemma EqJet.add {n : ℕ} {f g a b : MvPowerSeries σ K}
    (h : EqJet n f g) (h' : EqJet n a b) : EqJet n (f+a) (g+b) := by
  intro d hd; simp only [map_add,h d hd,h' d hd]
lemma EqJet.sub {n : ℕ} {f g a b : MvPowerSeries σ K}
    (h : EqJet n f g) (h' : EqJet n a b) : EqJet n (f-a) (g-b) := by
  intro d hd; simp only [map_sub,h d hd,h' d hd]
lemma EqJet.neg {n : ℕ} {f g : MvPowerSeries σ K} (h : EqJet n f g) : EqJet n (-f) (-g) := by
  intro d hd; simp only [map_neg,h d hd]
lemma EqJet.mul_left {n : ℕ} {f g : MvPowerSeries σ K} (h : EqJet n f g) (a : MvPowerSeries σ K) :
    EqJet n (a*f) (a*g) := by
  rw [eqJet_iff_order] at h ⊢
  rw [←mul_sub]
  exact le_trans (le_trans h (le_add_left le_rfl)) le_order_mul
lemma EqJet.mul_right {n : ℕ} {f g : MvPowerSeries σ K} (h : EqJet n f g) (a : MvPowerSeries σ K) :
    EqJet n (f*a) (g*a) := by simpa only [mul_comm] using h.mul_left a
lemma EqJet.mul {n : ℕ} {f g a b : MvPowerSeries σ K}
    (h : EqJet n f g) (h' : EqJet n a b) : EqJet n (f*a) (g*b) :=
  (h.mul_right a).trans (h'.mul_left g)
lemma EqJet.sum {ι : Type*} {n : ℕ} (s : Finset ι) (f g : ι → MvPowerSeries σ K)
    (h : ∀ i∈s, EqJet n (f i) (g i)) : EqJet n (∑i∈s,f i) (∑i∈s,g i) := by
  intro d hd; simp only [map_sum]; exact Finset.sum_congr rfl fun i hi => h i hi d hd

lemma EqJet.subst_left {n : ℕ} {f g : MvPowerSeries σ K} (h : EqJet n f g)
    (a : σ → MvPowerSeries τ K) (ha : HasSubst a) (ha0 : ∀i,(a i).constantCoeff=0) :
    EqJet n (f.subst a) (g.subst a) := by
  rw [eqJet_iff_order] at h ⊢
  rw [←subst_sub ha]
  have ho : (1 : ℕ∞) ≤ ⨅ i, (a i).order := le_iInf fun i =>
    one_le_order_iff_constCoeff_eq_zero.mpr (ha0 i)
  exact (h.trans (by simpa [mul_comm] using mul_le_mul_right ho (f-g).order)).trans
    (le_order_subst ha (f-g))

lemma EqJet.subst_right [Finite τ] {n : ℕ} (f : MvPowerSeries σ K)
    (a b : σ → MvPowerSeries τ K) (ha : HasSubst a) (hb : HasSubst b)
    (h : ∀i,EqJet n (a i) (b i)) : EqJet n (f.subst a) (f.subst b) := by
  rw [eqJet_iff_trunc,
    truncTotal_subst_eq_truncTotal_subst_truncTotal_of_le ha (x:=fun _=>n) (fun _=>le_rfl),
    truncTotal_subst_eq_truncTotal_subst_truncTotal_of_le hb (x:=fun _=>n) (fun _=>le_rfl)]
  congr 2
  funext i
  exact congrArg MvPolynomial.toMvPowerSeries ((eqJet_iff_trunc n _ _).mp (h i))

lemma eqJet_zero_mul {n m : ℕ} {f g : MvPowerSeries σ K}
    (hf : EqJet n f 0) (hg : EqJet m g 0) : EqJet (n+m) (f*g) 0 := by
  rw [eqJet_iff_order,sub_zero] at hf hg ⊢
  exact (show ((n+m : ℕ) : ℕ∞) ≤ f.order+g.order by simpa using add_le_add hf hg).trans le_order_mul

lemma eqJet_one_zero (f : MvPowerSeries σ K) (hf : f.constantCoeff=0) : EqJet 1 f 0 := by
  rw [eqJet_iff_order,sub_zero]
  exact one_le_order_iff_constCoeff_eq_zero.mpr hf

lemma eqJet_sub_zero {n : ℕ} {f g : MvPowerSeries σ K} : EqJet n (f-g) 0 ↔ EqJet n f g := by
  constructor <;> intro h d hd
  · exact sub_eq_zero.mp (by simpa only [map_sub,map_zero] using h d hd)
  · simp only [map_sub,map_zero,h d hd,sub_self]

lemma eqJet_subst_constant (f : MvPowerSeries σ K) (a : σ → MvPowerSeries τ K)
    (ha : HasSubst a) (ha0 : ∀i,(a i).constantCoeff=0) :
    EqJet 1 (f.subst a) (C f.constantCoeff) := by
  rw [←eqJet_sub_zero]
  apply eqJet_one_zero
  simp only [map_sub,constantCoeff_C]
  exact sub_eq_zero.mpr (HeightThree.OriginalDifferentialSupport.constantCoeff_subst_zero_axis a ha ha0 f)

lemma coeff_linear_mul (f g : MvPowerSeries σ K) (i : σ) :
    coeff (Finsupp.single i 1) (f*g)=
      f.constantCoeff*coeff (Finsupp.single i 1) g+
      g.constantCoeff*coeff (Finsupp.single i 1) f := by
  have h (a : MvPowerSeries σ K) : constantCoeff (pderiv i a)=coeff (Finsupp.single i 1) a := by
    rw [←coeff_zero_eq_constantCoeff,coeff_pderiv]; simp
  rw [←h,Derivation.leibniz,smul_eq_mul,smul_eq_mul,map_add,map_mul,map_mul,h,h]

lemma subst_first_order_polynomial [Fintype σ] [Finite τ]
    (f : MvPolynomial σ K) (n : ℕ)
    (a b : σ → MvPowerSeries τ K) (ha0 : ∀i,(a i).constantCoeff=0)
    (hb0 : ∀i,(b i).constantCoeff=0) (hab : ∀i,EqJet n (a i) (b i)) :
    EqJet (n+1) ((f : MvPowerSeries σ K).subst a - (f : MvPowerSeries σ K).subst b)
      (∑i, C (coeff (Finsupp.single i 1) (f : MvPowerSeries σ K))*(a i-b i)) := by
  classical
  have ha : HasSubst a := hasSubst_of_constantCoeff_zero ha0
  have hb : HasSubst b := hasSubst_of_constantCoeff_zero hb0
  induction f using MvPolynomial.induction_on with
  | C c =>
    simp only [MvPolynomial.coe_C,subst_C,coeff_C,Finsupp.single_eq_zero,one_ne_zero,
      ite_false,map_zero,zero_mul,Finset.sum_const_zero,sub_self]
    exact EqJet.refl _ _
  | add f g hf hg =>
    convert hf.add hg using 1
    · simp only [MvPolynomial.coe_add,subst_add ha,subst_add hb]; ring
    · simp only [MvPolynomial.coe_add,map_add,add_mul,Finset.sum_add_distrib]
  | mul_X f j hf =>
    have h1 : EqJet (n+1) (((f : MvPowerSeries σ K).subst a-C (f : MvPowerSeries σ K).constantCoeff)*(a j-b j)) 0 := by
      simpa only [add_comm] using eqJet_zero_mul
        (eqJet_sub_zero.mpr (eqJet_subst_constant _ a ha ha0)) (eqJet_sub_zero.mpr (hab j))
    have h2 : EqJet (n+1) (((f : MvPowerSeries σ K).subst a-(f : MvPowerSeries σ K).subst b)*b j) 0 :=
      eqJet_zero_mul (eqJet_sub_zero.mpr (EqJet.subst_right _ a b ha hb hab))
        (eqJet_one_zero _ (hb0 j))
    have he : ((f : MvPowerSeries σ K).subst a*a j-(f : MvPowerSeries σ K).subst b*b j) -
        C (f : MvPowerSeries σ K).constantCoeff*(a j-b j)=
      (((f : MvPowerSeries σ K).subst a-C (f : MvPowerSeries σ K).constantCoeff)*(a j-b j))+
      (((f : MvPowerSeries σ K).subst a-(f : MvPowerSeries σ K).subst b)*b j) := by ring
    have hh₀ : EqJet (n+1)
        (((f : MvPowerSeries σ K).subst a*a j-(f : MvPowerSeries σ K).subst b*b j) -
          C (f : MvPowerSeries σ K).constantCoeff*(a j-b j)) 0 := by
      rw [he]; simpa using h1.add h2
    have hh := eqJet_sub_zero.mp hh₀
    convert hh using 1
    · simp only [MvPolynomial.coe_mul,MvPolynomial.coe_X,subst_mul ha,subst_mul hb,
        subst_X ha,subst_X hb]
    · simp only [MvPolynomial.coe_mul,MvPolynomial.coe_X]
      simp [coeff_linear_mul, coeff_index_single_X,apply_ite]

lemma subst_first_order [Fintype σ] [Finite τ]
    (f : MvPowerSeries σ K) (n : ℕ)
    (a b : σ → MvPowerSeries τ K) (ha0 : ∀i,(a i).constantCoeff=0)
    (hb0 : ∀i,(b i).constantCoeff=0) (hab : ∀i,EqJet n (a i) (b i)) :
    EqJet (n+1) (f.subst a - f.subst b)
      (∑i, C (coeff (Finsupp.single i 1) f)*(a i-b i)) := by
  classical
  let : UniformSpace K := ⊥
  let : DiscreteUniformity K := ⟨rfl⟩
  open MvPowerSeries.WithPiTopology in
  have hc₁ : Continuous (fun f : MvPowerSeries σ K => f.subst a - f.subst b) :=
    (continuous_subst (hasSubst_of_constantCoeff_zero ha0)).sub
      (continuous_subst (hasSubst_of_constantCoeff_zero hb0))
  intro d hd
  have hc₂ : Continuous (fun f : MvPowerSeries σ K =>
      ∑i, C (coeff (Finsupp.single i 1) f)*(a i-b i)) := by
    apply continuous_finsetSum
    intro i hi
    exact ((MvPowerSeries.WithPiTopology.continuous_C).comp
      (MvPowerSeries.WithPiTopology.continuous_coeff K _)).mul_const _
  have hh := MvPowerSeries.WithPiTopology.denseRange_toMvPowerSeries.equalizer
    ((MvPowerSeries.WithPiTopology.continuous_coeff K d).comp hc₁)
    ((MvPowerSeries.WithPiTopology.continuous_coeff K d).comp hc₂)
    (by funext g; exact subst_first_order_polynomial g n a b ha0 hb0 hab d hd)
  exact congrFun hh f

lemma law_first_order [Finite τ] (F : FormalGroup K) (n : ℕ)
    (a b : Fin 2 → MvPowerSeries τ K) (ha0 : ∀i,(a i).constantCoeff=0)
    (hb0 : ∀i,(b i).constantCoeff=0) (hab : ∀i,EqJet n (a i) (b i)) :
    EqJet (n+1) (F.toPowerSeries.subst a - F.toPowerSeries.subst b)
      ((a 0-b 0)+(a 1-b 1)) := by
  simpa only [Fin.sum_univ_two,F.lin_coeff_X,F.lin_coeff_Y,map_one,one_mul]
    using subst_first_order F.toPowerSeries n a b ha0 hb0 hab

lemma EqJet.mul_leading {m n : ℕ} {f g a b : MvPowerSeries σ K}
    (hfg : EqJet (m+1) f g) (hab : EqJet (n+1) a b)
    (hg : EqJet m g 0) (ha : EqJet n a 0) : EqJet (m+n+1) (f*a) (g*b) := by
  rw [←eqJet_sub_zero]
  have he : f*a-g*b=(f-g)*a+g*(a-b) := by ring
  rw [he]
  have h₁ := eqJet_zero_mul (eqJet_sub_zero.mpr hfg) ha
  have h₂ := eqJet_zero_mul hg (eqJet_sub_zero.mpr hab)
  have h₁' : EqJet (m+n+1) ((f-g)*a) 0 := by convert h₁ using 1; omega
  have h₂' : EqJet (m+n+1) (g*(a-b)) 0 := h₂
  simpa only [add_zero] using h₁'.add h₂'

lemma eqJet_pow_zero (f : MvPowerSeries σ K) (hf : f.constantCoeff=0) (n : ℕ) :
    EqJet n (f^n) 0 := by
  rw [eqJet_iff_order,sub_zero]
  exact le_order_pow_of_constantCoeff_eq_zero n hf

lemma EqJet.pow_leading {f g : MvPowerSeries σ K} (h : EqJet 2 f g)
    (hf : f.constantCoeff=0) (hg : g.constantCoeff=0) (n : ℕ) :
    EqJet (n+1) (f^n) (g^n) := by
  induction n with
  | zero => exact EqJet.refl _ _
  | succ n ih =>
    simpa only [pow_succ] using ih.mul_leading h
      (eqJet_pow_zero g hg n) (eqJet_one_zero f hf)

lemma leading_part (f : MvPowerSeries σ K) (n : ℕ) (h : EqJet n f 0) :
    EqJet (n+1) f (f.homogeneousComponent n) := by
  intro d hd
  rw [coeff_homogeneousComponent]
  split_ifs with he
  · rfl
  · have hh : d.degree<n := by omega
    simpa only [map_zero] using h d hh

lemma homogeneous_eq_of_jet {f g : MvPowerSeries σ K} {n : ℕ}
    (hf : f.IsHomogeneous n) (hg : g.IsHomogeneous n) (h : EqJet (n+1) f g) : f=g := by
  ext d
  by_cases hd : d.degree=n
  · exact h d (by omega)
  · rw [hf.coeff_eq_zero hd,hg.coeff_eq_zero hd]

section Field
variable {K : Type*} [Field K]
open HeightThree.HomogeneousCocycle

lemma subst_homogeneous_leading (D : MvPowerSeries (Fin 2) K) (n : ℕ)
    (hD : D.IsHomogeneous n) (a b : Fin 2 → MvPowerSeries σ K)
    (ha : ∀i,(a i).constantCoeff=0) (hb : ∀i,(b i).constantCoeff=0)
    (hab : ∀i,EqJet 2 (a i) (b i)) : EqJet (n+1) (D.subst a) (D.subst b) := by
  classical
  have ha' := hasSubst_of_constantCoeff_zero ha
  have hb' := hasSubst_of_constantCoeff_zero hb
  have ea : a=![a 0,a 1] := by ext i; fin_cases i <;> rfl
  have eb : b=![b 0,b 1] := by ext i; fin_cases i <;> rfl
  rw [homogeneous_sum D n hD,←coe_substAlgHom ha',←coe_substAlgHom hb',map_sum,map_sum]
  apply EqJet.sum
  intro i hi
  simp only [coe_substAlgHom]
  rw [ea,eb,subst_monomial_pair _ _ _ _ _ (ha 0) (ha 1),
    subst_monomial_pair _ _ _ _ _ (hb 0) (hb 1)]
  have hh := ((hab 0).pow_leading (ha 0) (hb 0) i).mul_leading
    ((hab 1).pow_leading (ha 1) (hb 1) (n-i))
    (eqJet_pow_zero (b 0) (hb 0) i) (eqJet_pow_zero (a 1) (ha 1) (n-i))
  have hi' : i≤n := by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hi
  simpa only [Nat.add_sub_of_le hi',mul_assoc] using hh.mul_left (C _)

lemma homogeneous_subst_linear (D : MvPowerSeries (Fin 2) K) (n : ℕ)
    (hD : D.IsHomogeneous n) (a : Fin 2 → MvPowerSeries σ K)
    (ha : ∀i,(a i).constantCoeff=0) (haH : ∀i,(a i).IsHomogeneous 1) :
    (D.subst a).IsHomogeneous n := by
  classical
  have ha' := hasSubst_of_constantCoeff_zero ha
  have ea : a=![a 0,a 1] := by ext i; fin_cases i <;> rfl
  apply homogeneous_of_coeff
  intro d hd
  rw [homogeneous_sum D n hD,←coe_substAlgHom ha',map_sum,map_sum]
  apply Finset.sum_eq_zero
  intro i hi
  simp only [coe_substAlgHom]
  rw [ea,subst_monomial_pair _ _ _ _ _ (ha 0) (ha 1),mul_assoc]
  have hi' : i≤n := by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hi
  have h₁ : ((a 0)^i).IsHomogeneous i := by
    have hh : ((a 0)^i).IsHomogeneous (1*i) := by exact homogeneous_pow (haH 0) i
    rw [one_mul] at hh; exact @hh
  have h₂ : ((a 1)^(n-i)).IsHomogeneous (n-i) := by
    have hh : ((a 1)^(n-i)).IsHomogeneous (1*(n-i)) := by exact homogeneous_pow (haH 1) (n-i)
    rw [one_mul] at hh; exact @hh
  have h₃ : ((a 0)^i*(a 1)^(n-i)).IsHomogeneous n := by
    have hh : ((a 0)^i*(a 1)^(n-i)).IsHomogeneous (i+(n-i)) := by exact h₁.mul h₂
    rw [Nat.add_sub_of_le hi'] at hh; exact @hh
  rw [coeff_C_mul,h₃.coeff_eq_zero hd,mul_zero]

end Field
end HeightThree.HondaJets

end

end OAI
