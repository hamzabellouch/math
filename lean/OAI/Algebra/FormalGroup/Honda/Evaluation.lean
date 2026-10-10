import OAI.Algebra.FormalGroup.Honda.ArtinianRigidity

namespace OAI

noncomputable section

namespace HeightThree.NilpotentEvaluation
open MvPowerSeries
variable {K R S : Type*} [CommRing K] [CommRing R] [CommRing S]

def constantHom [Algebra K R] : PowerSeries R →ₐ[K] R where
  __ := (MvPowerSeries.constantCoeff : PowerSeries R →+* R)
  commutes' r := by simp [MvPowerSeries.algebraMap_apply]

lemma constantsHasSubst (a : Fin 2 → R) (h : ∀ i, IsNilpotent (a i)) :
    HasSubst (fun i => (C (a i) : PowerSeries R)) :=
  hasSubst_of_constantCoeff_nilpotent (fun i => by simpa only [constantCoeff_C] using h i)

def eval [Algebra K R] (a : Fin 2 → R) (h : ∀ i, IsNilpotent (a i)) :
    MvPowerSeries (Fin 2) K →ₐ[K] R :=
  constantHom.comp (substAlgHom (constantsHasSubst a h))

@[simp] lemma eval_X [Algebra K R] (a : Fin 2 → R) (h : ∀ i, IsNilpotent (a i)) (i : Fin 2) :
    eval (K := K) a h (X i) = a i := by
  change constantCoeff (substAlgHom (constantsHasSubst a h) (X i)) = a i
  rw [substAlgHom_X,constantCoeff_C]

@[simp] lemma eval_C [Algebra K R] (a : Fin 2 → R) (h : ∀ i, IsNilpotent (a i)) (c : K) :
    eval a h (C c) = algebraMap K R c := by
  change eval a h (algebraMap K (MvPowerSeries (Fin 2) K) c) = _
  exact AlgHom.commutes _ c

lemma degree_two (d : Fin 2 →₀ ℕ) : d.degree = d 0+d 1 := by
  classical
  change d.sum (fun _ n => n) = _
  rw [Finsupp.sum_fintype]
  · exact Fin.sum_univ_two _
  · simp

lemma tail_rect (f : MvPowerSeries (Fin 2) K) (N : ℕ) :
    ∃ g h : MvPowerSeries (Fin 2) K,
      f-(↑(f.truncTotal (2*N)) : MvPowerSeries (Fin 2) K) = X 0^N*g+X 1^N*h := by
  classical
  let t := f-(↑(f.truncTotal (2*N)) : MvPowerSeries (Fin 2) K)
  let t₀ : MvPowerSeries (Fin 2) K := fun d => if N ≤ d 0 then coeff d t else 0
  let t₁ := t-t₀
  have h₀ : X 0^N ∣ t₀ := by
    apply X_pow_dvd_iff.mpr
    intro d hd
    change (if N ≤ d 0 then coeff d t else 0) = 0
    simp [not_le.mpr hd]
  have h₁ : X 1^N ∣ t₁ := by
    apply X_pow_dvd_iff.mpr
    intro d hd
    change coeff d t-(if N ≤ d 0 then coeff d t else 0) = 0
    by_cases hN : N ≤ d 0
    · simp [hN]
    · have ht : d.degree < 2*N := by rw [degree_two]; omega
      simp only [ite_eq_right hN,t,map_sub,MvPolynomial.coeff_coe,coeff_truncTotal _ ht,sub_self]
  obtain ⟨g,hg⟩ := h₀
  obtain ⟨h,hh⟩ := h₁
  refine ⟨g,h,?_⟩
  rw [←hg,←hh]
  dsimp [t₁,t]
  ring

lemma hom_apply_eq_trunc [Algebra K R] (φ : MvPowerSeries (Fin 2) K →ₐ[K] R)
    (N : ℕ) (hN : ∀ i : Fin 2, φ (X i)^N = 0) (f : MvPowerSeries (Fin 2) K) :
    φ f = φ (↑(f.truncTotal (2*N)) : MvPowerSeries (Fin 2) K) := by
  obtain ⟨g,h,he⟩ := tail_rect f N
  have hh := congrArg φ he
  simp only [map_sub,map_add,map_mul,map_pow,hN,zero_mul,add_zero] at hh
  exact sub_eq_zero.mp hh

lemma hom_ext_nilpotent [Algebra K R] (φ ψ : MvPowerSeries (Fin 2) K →ₐ[K] R)
    (hφ : ∀ i : Fin 2, IsNilpotent (φ (X i))) (he : ∀ i : Fin 2, φ (X i)=ψ (X i)) : φ=ψ := by
  obtain ⟨a,ha⟩ := hφ 0
  obtain ⟨b,hb⟩ := hφ 1
  let N := max a b
  have hN : ∀ i : Fin 2, φ (X i)^N=0 := by
    intro i; fin_cases i
    · exact pow_eq_zero_of_le (le_max_left _ _) ha
    · exact pow_eq_zero_of_le (le_max_right _ _) hb
  have hN' : ∀ i : Fin 2, ψ (X i)^N=0 := by simpa only [he] using hN
  have hpoly : ∀ f : MvPolynomial (Fin 2) K,
      φ (f : MvPowerSeries (Fin 2) K) = ψ (f : MvPowerSeries (Fin 2) K) := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C c => simpa only [MvPolynomial.coe_C,MvPowerSeries.c_eq_algebraMap] using
        (φ.commutes c).trans (ψ.commutes c).symm
    | add f g hf hg => simp only [MvPolynomial.coe_add,map_add,hf,hg]
    | mul_X f i hf => simp only [MvPolynomial.coe_mul,MvPolynomial.coe_X,map_mul,hf,he]
  ext f
  rw [hom_apply_eq_trunc φ N hN f, hom_apply_eq_trunc ψ N hN' f]
  exact hpoly _

lemma eval_natural [Algebra K R] [Algebra K S] (π : R →ₐ[K] S)
    (a : Fin 2 → R) (h : ∀ i, IsNilpotent (a i)) :
    π.comp (eval a h) = eval (fun i => π (a i)) (fun i => (h i).map π.toRingHom) := by
  apply hom_ext_nilpotent
  · intro i; simpa using (h i).map π.toRingHom
  · intro i; simp

lemma eval_zero [Algebra K R] (h : ∀ _ : Fin 2, IsNilpotent (0 : R)) (f : MvPowerSeries (Fin 2) K) :
    eval (fun _ => (0 : R)) h f = algebraMap K R (constantCoeff f) := by
  let ψ : MvPowerSeries (Fin 2) K →ₐ[K] R :=
    { __ := (algebraMap K R).comp constantCoeff
      commutes' := by intro r; simp [MvPowerSeries.algebraMap_apply] }
  have he : eval (fun _ => (0 : R)) h = ψ := by
    apply hom_ext_nilpotent
    · intro i; simp
    · intro i; simp [ψ]
  exact congrArg (fun φ : MvPowerSeries (Fin 2) K →ₐ[K] R => φ f) he

lemma linear_coeff_mul_X (f : MvPowerSeries (Fin 2) K) (i j : Fin 2) :
    coeff (Finsupp.single j 1) (f * X i) = if i=j then constantCoeff f else 0 := by
  classical
  by_cases hij : i=j
  · subst j; simp [X,coeff_mul_monomial]
  · have hn : ¬Finsupp.single i 1 ≤ (Finsupp.single j 1 : Fin 2 →₀ ℕ) := by
      intro h
      have hi := h i
      simp [hij] at hi
    simp [X,coeff_mul_monomial,hn,hij]

theorem hom_difference_small [Algebra K R] (π : R →+* S) (ρ : R →ₐ[K] K)
    (ann : ∀ a b, π a=0 → ρ b=0 → a*b=0)
    (φ ψ : MvPowerSeries (Fin 2) K →ₐ[K] R)
    (hπ : ∀ f, π (φ f)=π (ψ f))
    (hφ : ∀ f, ρ (φ f)=constantCoeff f)
    (hψ : ∀ f, ρ (ψ f)=constantCoeff f)
    (hnil : ∀ i : Fin 2, IsNilpotent (φ (X i)))
    (f : MvPowerSeries (Fin 2) K) :
    φ f-ψ f = (φ (X 0)-ψ (X 0))*algebraMap K R (coeff (Finsupp.single 0 1) f) +
      (φ (X 1)-ψ (X 1))*algebraMap K R (coeff (Finsupp.single 1 1) f) := by
  classical
  have poly : ∀ f : MvPolynomial (Fin 2) K,
      φ (f : MvPowerSeries (Fin 2) K)-ψ (f : MvPowerSeries (Fin 2) K) =
      (φ (X 0)-ψ (X 0))*algebraMap K R (coeff (Finsupp.single 0 1) (f : MvPowerSeries (Fin 2) K)) +
      (φ (X 1)-ψ (X 1))*algebraMap K R (coeff (Finsupp.single 1 1) (f : MvPowerSeries (Fin 2) K)) := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C c =>
      simp only [MvPolynomial.coe_C]
      rw [show φ (C c)=algebraMap K R c from φ.commutes c,
        show ψ (C c)=algebraMap K R c from ψ.commutes c]
      simp [coeff_C]
    | add f g hf hg =>
      simp only [MvPolynomial.coe_add,map_add] at *
      linear_combination hf+hg
    | mul_X f i hf =>
      let F : MvPowerSeries (Fin 2) K := f
      have hz₁ : (φ F-ψ F)*φ (X i)=0 :=
        ann _ _ (by simp only [map_sub,hπ,sub_self]) (by rw [hφ,constantCoeff_X])
      have hz₂ : (φ (X i)-ψ (X i))*(ψ F-algebraMap K R (constantCoeff F))=0 :=
        ann _ _ (by simp only [map_sub,hπ,sub_self]) (by simp [hψ])
      have he : φ (F*X i)-ψ (F*X i) =
          (φ (X i)-ψ (X i))*algebraMap K R (constantCoeff F) := by
        simp only [map_mul]
        linear_combination hz₁+hz₂
      simp only [MvPolynomial.coe_mul,MvPolynomial.coe_X]
      change φ (F*X i)-ψ (F*X i) = _
      rw [he]
      change _ = (φ (X 0)-ψ (X 0))*algebraMap K R (coeff (Finsupp.single 0 1) (F*X i)) +
        (φ (X 1)-ψ (X 1))*algebraMap K R (coeff (Finsupp.single 1 1) (F*X i))
      rw [linear_coeff_mul_X,linear_coeff_mul_X]
      fin_cases i <;> simp

  have hnil' : ∀ i : Fin 2, IsNilpotent (ψ (X i)) := by
    intro i
    have hd : π (φ (X i)-ψ (X i))=0 := by simp only [map_sub,hπ,sub_self]
    have hz : (φ (X i)-ψ (X i))^2=0 := by
      rw [pow_two]; exact ann _ _ hd (by rw [map_sub,hφ,hψ,sub_self])
    have hh := (Commute.all _ _).isNilpotent_sub (hnil i) (show IsNilpotent (φ (X i)-ψ (X i)) from ⟨2,hz⟩)
    simpa only [sub_sub_cancel] using hh
  obtain ⟨a,ha⟩ := hnil 0
  obtain ⟨b,hb⟩ := hnil 1
  obtain ⟨c,hc⟩ := hnil' 0
  obtain ⟨d,hd⟩ := hnil' 1
  let N := max (max a b) (max c d)+1
  have hN : ∀ i : Fin 2, φ (X i)^N=0 := by
    intro i; fin_cases i
    · exact pow_eq_zero_of_le (by dsimp [N]; omega) ha
    · exact pow_eq_zero_of_le (by dsimp [N]; omega) hb
  have hN' : ∀ i : Fin 2, ψ (X i)^N=0 := by
    intro i; fin_cases i
    · exact pow_eq_zero_of_le (by dsimp [N]; omega) hc
    · exact pow_eq_zero_of_le (by dsimp [N]; omega) hd
  rw [hom_apply_eq_trunc φ N hN f,hom_apply_eq_trunc ψ N hN' f,poly]
  simp only [MvPolynomial.coeff_coe,coeff_truncTotal _ (show (Finsupp.single (0 : Fin 2) 1).degree < 2*N by simp; dsimp [N]; omega),
    coeff_truncTotal _ (show (Finsupp.single (1 : Fin 2) 1).degree < 2*N by simp; dsimp [N]; omega)]

lemma eval_augmentation [Algebra K R] (ρ : R →ₐ[K] K)
    (a : Fin 2 → R) (h : ∀ i, IsNilpotent (a i)) (ha : ∀ i, ρ (a i)=0)
    (f : MvPowerSeries (Fin 2) K) : ρ (eval a h f)=constantCoeff f := by
  let ε : MvPowerSeries (Fin 2) K →ₐ[K] K :=
    { __ := constantCoeff
      commutes' := by intro r; simp [MvPowerSeries.algebraMap_apply] }
  have he : ρ.comp (eval a h)=ε := by
    apply hom_ext_nilpotent
    · intro i; simpa using (h i).map ρ.toRingHom
    · intro i; simp [ε,ha]
  exact congrArg (fun φ : MvPowerSeries (Fin 2) K →ₐ[K] K => φ f) he

theorem correct_parameters [Algebra K R] [Algebra K S]
    (π : R →ₐ[K] S) (ρ : R →ₐ[K] K)
    (kle : ∀ a, π a=0 → ρ a=0)
    (ann : ∀ a b, π a=0 → ρ b=0 → a*b=0)
    (φ : MvPowerSeries (Fin 2) K →ₐ[K] R)
    (hφ : ∀ f, ρ (φ f)=constantCoeff f)
    (hnil : ∀ i : Fin 2, IsNilpotent (φ (X i)))
    (c g : MvPowerSeries (Fin 2) K) (hc : c=X 1+X 0*g)
    (b₀ b₁ : R) (hb₀ : π b₀=π (φ (X 0))) (hb₁ : π b₁=π (φ c)) :
    ∃ ψ : MvPowerSeries (Fin 2) K →ₐ[K] R,
      π.comp ψ=π.comp φ ∧ (∀ f, ρ (ψ f)=constantCoeff f) ∧ ψ (X 0)=b₀ ∧ ψ c=b₁ := by
  let d₀ := b₀-φ (X 0)
  let d₁ := b₁-φ c-d₀*algebraMap K R (constantCoeff g)
  have hd₀ : π d₀=0 := by simp [d₀,hb₀]
  have hd₁ : π d₁=0 := by simp [d₁,hb₁,hd₀]
  have hdnil₀ : IsNilpotent d₀ := ⟨2,by rw [pow_two]; exact ann _ _ hd₀ (kle _ hd₀)⟩
  have hdnil₁ : IsNilpotent d₁ := ⟨2,by rw [pow_two]; exact ann _ _ hd₁ (kle _ hd₁)⟩
  let a : Fin 2 → R := ![φ (X 0)+d₀,φ (X 1)+d₁]
  have hanil : ∀ i, IsNilpotent (a i) := by
    intro i; fin_cases i
    · exact (Commute.all _ _).isNilpotent_add (hnil 0) hdnil₀
    · exact (Commute.all _ _).isNilpotent_add (hnil 1) hdnil₁
  let ψ : MvPowerSeries (Fin 2) K →ₐ[K] R := eval a hanil
  have hψπ : π.comp ψ=π.comp φ := by
    apply hom_ext_nilpotent
    · intro i; simpa [ψ] using (hanil i).map π.toRingHom
    · intro i; fin_cases i <;> simp [ψ,a,hd₀,hd₁]
  have hψρ : ∀ f, ρ (ψ f)=constantCoeff f := by
    apply eval_augmentation ρ a hanil
    intro i; fin_cases i <;> simp [a,hφ,kle _ hd₀,kle _ hd₁]
  have hlin₀ : coeff (Finsupp.single 0 1) c=constantCoeff g := by
    rw [hc,mul_comm (X 0) g,map_add,linear_coeff_mul_X]
    simp [coeff_index_single_X]
  have hlin₁ : coeff (Finsupp.single 1 1) c=1 := by
    rw [hc,mul_comm (X 0) g,map_add,linear_coeff_mul_X]
    simp
  have he := hom_difference_small π.toRingHom ρ ann ψ φ
    (fun f => congrArg (fun η : MvPowerSeries (Fin 2) K →ₐ[K] S => η f) hψπ)
    hψρ hφ (by intro i; simpa [ψ] using hanil i) c
  rw [hlin₀,hlin₁,map_one,mul_one] at he
  have hx₀ : ψ (X 0)-φ (X 0)=d₀ := by simp [ψ,a]
  have hx₁ : ψ (X 1)-φ (X 1)=d₁ := by simp [ψ,a]
  rw [hx₀,hx₁] at he
  refine ⟨ψ,hψπ,hψρ,?_,?_⟩
  · simp [ψ,a,d₀]
  · dsimp [d₁] at he
    linear_combination he

end HeightThree.NilpotentEvaluation

end

end OAI
