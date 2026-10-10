import OAI.Algebra.FormalGroup.Honda.ChainRule

namespace OAI

noncomputable section

namespace HeightThree.HomogeneousCocycle
open MvPowerSeries
variable {K σ τ : Type*} [Field K]

lemma degree_pair (d : Fin 2 →₀ ℕ) : d.degree=d 0+d 1 := by
  rw [Finsupp.degree_eq_sum]
  simp

lemma pair_exp (d : Fin 2 →₀ ℕ) :
    d=Finsupp.single 0 (d 0)+Finsupp.single 1 (d 1) := by
  ext i; fin_cases i <;> simp

lemma monomial_pair (i j : ℕ) (a : K) :
    monomial (Finsupp.single 0 i+Finsupp.single 1 j) a =
      C a * (X (0 : Fin 2))^i * X 1^j := by
  rw [←monomial_zero_eq_C_apply,X_pow_eq,X_pow_eq,
    monomial_mul_monomial,monomial_mul_monomial]
  simp

lemma homogeneous_sum (D : MvPowerSeries (Fin 2) K) (n : ℕ) (hD : D.IsHomogeneous n) :
    D=∑ i ∈ Finset.range (n+1), C (coeff (Finsupp.single 0 i+Finsupp.single 1 (n-i)) D) *
      X 0^i * X 1^(n-i) := by
  classical
  simp_rw [←monomial_pair]
  ext d
  rw [map_sum]
  by_cases hd : d.degree=n
  · have he : n-d 0=d 1 := by rw [←hd,degree_pair]; omega
    have hi : d 0∈Finset.range (n+1) := by simp only [Finset.mem_range]; rw [←hd,degree_pair]; omega
    rw [Finset.sum_eq_single (d 0)]
    · rw [he,←pair_exp d,coeff_monomial_same]
    · intro i hi hne
      rw [coeff_monomial,ite_eq_right]
      intro h
      have hh := congrArg (fun e : Fin 2 →₀ ℕ => e 0) h
      simp at hh
      exact hne hh.symm
    · exact fun h => (h hi).elim
  · rw [hD.coeff_eq_zero hd]
    symm
    apply Finset.sum_eq_zero
    intro i hi
    rw [coeff_monomial,ite_eq_right]
    intro h
    apply hd
    rw [h,degree_pair]
    simp
    have : i≤n := by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hi
    omega

structure IsCocycle (p : ℕ) (D : MvPowerSeries (Fin 2) K) : Prop where
  zero_left : D.subst ![(0 : MvPowerSeries (Fin 1) K), X 0]=0
  zero_right : D.subst ![(X 0 : MvPowerSeries (Fin 1) K),0]=0
  symmetric : D.subst ![(X 1 : MvPowerSeries (Fin 2) K),X 0]=D
  associative :
    (D.subst ![(X 0 : MvPowerSeries (Fin 3) K),X 1]) + D.subst ![(X 0+X 1 : MvPowerSeries (Fin 3) K),X 2] =
    (D.subst ![(X 1 : MvPowerSeries (Fin 3) K),X 2]) + D.subst ![(X 0 : MvPowerSeries (Fin 3) K),X 1+X 2]
  trace_zero : ∑ i ∈ Finset.range p, D.subst ![C (i:K)*PowerSeries.X,PowerSeries.X]=0

lemma pair_subst_self (D : MvPowerSeries (Fin 2) K) : D.subst ![X 0,X 1]=D := by
  rw [show (![X 0,X 1] : Fin 2 → MvPowerSeries (Fin 2) K)=X by ext i; fin_cases i <;> rfl]
  exact congrFun MvPowerSeries.subst_self D

lemma derivative_cocycle (p : ℕ) (D : MvPowerSeries (Fin 2) K) (hD : IsCocycle p D) :
    pderiv (R := K) 1 D = (pderiv (R := K) 1 D).subst ![X 0+X 1,0] -
      (pderiv (R := K) 1 D).subst ![X 1,0] := by
  let a : Fin 2 → MvPowerSeries (Fin 3) K := ![X 0,X 1]
  let b : Fin 2 → MvPowerSeries (Fin 3) K := ![X 0+X 1,X 2]
  let c : Fin 2 → MvPowerSeries (Fin 3) K := ![X 1,X 2]
  let d : Fin 2 → MvPowerSeries (Fin 3) K := ![X 0,X 1+X 2]
  have ha : HasSubst a := hasSubst_of_constantCoeff_zero (by intro i; fin_cases i <;> simp [a])
  have hb : HasSubst b := hasSubst_of_constantCoeff_zero (by intro i; fin_cases i <;> simp [b])
  have hc : HasSubst c := hasSubst_of_constantCoeff_zero (by intro i; fin_cases i <;> simp [c])
  have hd : HasSubst d := hasSubst_of_constantCoeff_zero (by intro i; fin_cases i <;> simp [d])
  have hh := congrArg (pderiv (R := K) (2 : Fin 3)) hD.associative
  change pderiv (R := K) 2 (D.subst a+D.subst b)=pderiv (R := K) 2 (D.subst c+D.subst d) at hh
  simp only [map_add, OriginalDifferentialSupport.pderiv_subst a ha,
    OriginalDifferentialSupport.pderiv_subst b hb, OriginalDifferentialSupport.pderiv_subst c hc,
    OriginalDifferentialSupport.pderiv_subst d hd, Fin.sum_univ_two] at hh
  simp [a,b,c,d] at hh
  let e : Fin 3 → MvPowerSeries (Fin 2) K := ![X 0,X 1,0]
  have he : HasSubst e := hasSubst_of_constantCoeff_zero (by intro i; fin_cases i <;> simp [e])
  have hh' := congrArg (substAlgHom he) hh
  simp only [map_add,substAlgHom_apply] at hh'
  rw [subst_comp_subst_apply hb he,subst_comp_subst_apply hc he,subst_comp_subst_apply hd he] at hh'
  have eb : (fun i => (b i).subst e)=![X 0+X 1,0] := by
    ext i; fin_cases i <;> simp [b,e,subst_add he,subst_X he]
  have ec : (fun i => (c i).subst e)=![X 1,0] := by
    ext i; fin_cases i <;> simp [c,e,subst_X he]
  have ed : (fun i => (d i).subst e)=![X 0,X 1] := by
    ext i; fin_cases i <;> simp [d,e,subst_add he,subst_X he]
  rw [eb,ec,ed,pair_subst_self] at hh'
  exact eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using hh'.symm)

lemma derivative_monomial (a : K) (i j : ℕ) :
    pderiv (R := K) 1 (C a*(X (0 : Fin 2))^i*X 1^j)=
      C (a*(j:K))*X 0^i*X 1^(j-1) := by
  simp [Derivation.leibniz_pow,smul_eq_mul]
  ring

lemma subst_monomial_pair (c : K) (i j : ℕ) (a b : MvPowerSeries σ K)
    (ha : a.constantCoeff=0) (hb : b.constantCoeff=0) :
    (C c*(X (0 : Fin 2))^i*X 1^j).subst ![a,b] = C c*a^i*b^j := by
  have hs : HasSubst (![a,b] : Fin 2 → MvPowerSeries σ K) :=
    hasSubst_of_constantCoeff_zero (by intro i; fin_cases i <;> simp [ha,hb])
  simp only [←coe_substAlgHom hs,map_mul,map_pow,substAlgHom_X,
    Matrix.cons_val_zero,Matrix.cons_val_one]
  rw [show (substAlgHom hs) (C c)=C c from (substAlgHom hs).commutes c]

lemma homogeneous_derivative_axis (D : MvPowerSeries (Fin 2) K) (n : ℕ) (hn : 0<n)
    (hD : D.IsHomogeneous n) (a : MvPowerSeries σ K) (ha : a.constantCoeff=0) :
    (pderiv (R := K) 1 D).subst ![a,0] =
      C (coeff (Finsupp.single 0 (n-1)+Finsupp.single 1 1) D)*a^(n-1) := by
  classical
  have hs : HasSubst (![a,0] : Fin 2 → MvPowerSeries σ K) :=
    hasSubst_of_constantCoeff_zero (by intro i; fin_cases i <;> simp [ha])
  conv_lhs => rw [homogeneous_sum D n hD]
  simp only [map_sum,derivative_monomial]
  rw [←coe_substAlgHom hs,map_sum]
  simp only [coe_substAlgHom,subst_monomial_pair _ _ _ a 0 ha (map_zero _)]
  rw [Finset.sum_eq_single (n-1)]
  · have h1 : n-(n-1)=1 := by omega
    simp [h1]
  · intro i hi hne
    have hn1 : n-i≠1 := by omega
    by_cases hh : n-i=0
    · simp [hh]
    · have hn2 : n-i-1≠0 := by omega
      simp [hn2]
  · intro h
    exact (h (by simp only [Finset.mem_range]; omega)).elim

lemma derivative_shape (p : ℕ) (D : MvPowerSeries (Fin 2) K) (n : ℕ) (hn : 0<n)
    (hD : IsCocycle p D) (hH : D.IsHomogeneous n) :
    pderiv (R := K) 1 D = C (coeff (Finsupp.single 0 (n-1)+Finsupp.single 1 1) D) *
      ((X 0+X 1)^(n-1)-X 1^(n-1)) := by
  rw [derivative_cocycle p D hD,
    homogeneous_derivative_axis D n hn hH _ (by simp),
    homogeneous_derivative_axis D n hn hH _ (by simp)]
  ring

lemma homogeneous_of_coeff (f : MvPowerSeries σ K) (n : ℕ)
    (h : ∀ d, d.degree≠n → coeff d f=0) : f.IsHomogeneous n := by
  intro d hd
  have he : d.degree=n := by
    by_contra hn
    exact hd (h d hn)
  rwa [Finsupp.degree_eq_weight_one] at he

lemma homogeneous_sub {f g : MvPowerSeries σ K} {n : ℕ}
    (hf : f.IsHomogeneous n) (hg : g.IsHomogeneous n) : (f-g).IsHomogeneous n := by
  apply homogeneous_of_coeff
  intro d hd
  rw [map_sub,hf.coeff_eq_zero hd,hg.coeff_eq_zero hd,sub_self]

lemma homogeneous_smul (a : K) {f : MvPowerSeries σ K} {n : ℕ}
    (hf : f.IsHomogeneous n) : (a • f).IsHomogeneous n := by
  apply homogeneous_of_coeff
  intro d hd
  rw [map_smul,hf.coeff_eq_zero hd,smul_zero]

lemma homogeneous_X (i : σ) : (X i : MvPowerSeries σ K).IsHomogeneous 1 := by
  classical
  apply homogeneous_of_coeff
  intro d hd
  rw [coeff_X,ite_eq_right]
  intro he
  exact hd (by rw [he]; simp)

lemma homogeneous_one : (1 : MvPowerSeries σ K).IsHomogeneous 0 := by
  classical
  apply homogeneous_of_coeff
  intro d hd
  rw [coeff_one,ite_eq_right]
  intro he
  exact hd (by rw [he]; simp)

lemma homogeneous_pow {f : MvPowerSeries σ K} {d : ℕ} (hf : f.IsHomogeneous d) (n : ℕ) :
    (f^n).IsHomogeneous (d*n) := by
  induction n with
  | zero =>
    rw [pow_zero,Nat.mul_zero]
    exact homogeneous_one
  | succ n ih =>
    rw [pow_succ,Nat.mul_succ]
    exact ih.mul hf

def coboundary (n : ℕ) : MvPowerSeries (Fin 2) K := (X 0+X 1)^n-X 0^n-X 1^n

lemma homogeneous_coboundary (n : ℕ) : (coboundary (K := K) n).IsHomogeneous n := by
  have hx (i : Fin 2) : (X i : MvPowerSeries (Fin 2) K).IsHomogeneous 1 := by
    exact homogeneous_X i
  have hxpow (i : Fin 2) : ((X i : MvPowerSeries (Fin 2) K)^n).IsHomogeneous n := by
    have hh : ((X i : MvPowerSeries (Fin 2) K)^n).IsHomogeneous (1*n) := by
      exact homogeneous_pow (hx i) n
    rw [one_mul] at hh
    exact @hh
  have h01 : ((X (0 : Fin 2)+X 1 : MvPowerSeries (Fin 2) K)^n).IsHomogeneous n := by
    have hsum : (X (0 : Fin 2)+X 1 : MvPowerSeries (Fin 2) K).IsHomogeneous 1 :=
      IsHomogeneous.add (hx 0) (hx 1)
    have hh : ((X (0 : Fin 2)+X 1 : MvPowerSeries (Fin 2) K)^n).IsHomogeneous (1*n) := by
      exact homogeneous_pow hsum n
    rw [one_mul] at hh
    exact @hh
  unfold coboundary
  have hh : ((X (0 : Fin 2)+X 1 : MvPowerSeries (Fin 2) K)^n-X 0^n).IsHomogeneous n :=
    fun {_} h => homogeneous_sub h01 (hxpow 0) h
  exact fun {_} h => homogeneous_sub hh (hxpow 1) h

lemma derivative_coboundary (n : ℕ) :
    pderiv (R := K) 1 (coboundary (K := K) n) =
      C (n:K)*((X 0+X 1)^(n-1)-X 1^(n-1)) := by
  simp [coboundary,Derivation.leibniz_pow,smul_eq_mul]
  ring

lemma coeff_add_pow (n i j : ℕ) (hij : i+j=n) :
    coeff (Finsupp.single 0 i+Finsupp.single 1 j) ((X (0 : Fin 2)+X 1 : MvPowerSeries (Fin 2) K)^n)=
      (n.choose i : K) := by
  classical
  rw [add_pow,map_sum,Finset.sum_eq_single i]
  · have he : n-i=j := by omega
    rw [he]
    have hm : (X (0 : Fin 2) : MvPowerSeries (Fin 2) K)^i*X 1^j*(n.choose i : MvPowerSeries (Fin 2) K)=
        monomial (Finsupp.single 0 i+Finsupp.single 1 j) (n.choose i : K) := by
      rw [monomial_pair,map_natCast]
      ring
    rw [hm,coeff_monomial_same]
  · intro k hk hki
    have hm : (X (0 : Fin 2) : MvPowerSeries (Fin 2) K)^k*X 1^(n-k)*(n.choose k : MvPowerSeries (Fin 2) K)=
        monomial (Finsupp.single 0 k+Finsupp.single 1 (n-k)) (n.choose k : K) := by
      rw [monomial_pair,map_natCast]
      ring
    rw [hm,coeff_monomial,ite_eq_right]
    intro he
    have hh := congrArg (fun e : Fin 2 →₀ ℕ => e 0) he
    simp only [Finsupp.add_apply,Finsupp.single_eq_same,Finsupp.single_eq_of_ne (show (0:Fin 2)≠1 by decide),add_zero] at hh
    exact hki hh.symm
  · intro hi
    exact (hi (by simp only [Finset.mem_range]; omega)).elim

lemma derivative_zero_support (p : ℕ) [Fact p.Prime] [CharP K p]
    (f : MvPowerSeries σ K) (hf : ∀ i, pderiv (R := K) i f=0)
    (d : σ →₀ ℕ) (hd : coeff d f≠0) : ∀ i, p∣d i := by
  classical
  intro i
  by_cases hi : d i=0
  · rw [hi]; exact dvd_zero p
  let e := d.erase i+Finsupp.single i (d i-1)
  have he : e+Finsupp.single i 1=d := by
    ext j
    by_cases hj : j=i
    · subst j; simp [e,Nat.sub_add_cancel (by omega : 1≤d i)]
    · simp [e,hj]
  have hei : (e i : K)+1=(d i : K) := by
    have hh := congrArg (fun d : σ →₀ ℕ => d i) he
    simp only [Finsupp.add_apply,Finsupp.single_eq_same] at hh
    simpa only [Nat.cast_add,Nat.cast_one] using congrArg (fun m : ℕ => (m : K)) hh
  have hh := congrArg (coeff e) (hf i)
  rw [coeff_pderiv,he,hei,map_zero] at hh
  exact (CharP.cast_eq_zero_iff K p (d i)).mp ((mul_eq_zero.mp hh).resolve_left hd)

lemma derivative_symmetry (D : MvPowerSeries (Fin 2) K)
    (hD : D.subst ![X 1,X 0]=D) :
    pderiv (R := K) 0 D=(pderiv (R := K) 1 D).subst ![X 1,X 0] := by
  have hs : HasSubst (![X 1,X 0] : Fin 2 → MvPowerSeries (Fin 2) K) :=
    hasSubst_of_constantCoeff_zero (by intro i; fin_cases i <;> simp)
  have hh := congrArg (pderiv (R := K) (0 : Fin 2)) hD
  rw [OriginalDifferentialSupport.pderiv_subst _ hs] at hh
  simpa [Fin.sum_univ_two] using hh.symm

lemma coboundary_symmetric (n : ℕ) :
    (coboundary (K := K) n).subst ![X 1,X 0]=coboundary (K := K) n := by
  have hs : HasSubst (![X 1,X 0] : Fin 2 → MvPowerSeries (Fin 2) K) :=
    hasSubst_of_constantCoeff_zero (by intro i; fin_cases i <;> simp)
  simp only [coboundary,←coe_substAlgHom hs,map_sub,map_add,map_pow,substAlgHom_X,
    Matrix.cons_val_zero,Matrix.cons_val_one]
  rw [add_comm (X 1) (X 0)]
  ring

lemma homogeneous_derivative_zero (p : ℕ) [hp : Fact p.Prime] [CharP K p]
    (f : MvPowerSeries (Fin 2) K) (n : ℕ) (hn : ¬p∣n)
    (hH : f.IsHomogeneous n) (hf : ∀ i, pderiv (R := K) i f=0) : f=0 := by
  ext d
  rw [map_zero]
  by_contra hd
  have he := derivative_zero_support p f hf d hd
  apply hn
  have hdn : d.degree=n := by
    by_contra h
    exact hd (hH.coeff_eq_zero h)
  rw [←hdn,degree_pair]
  exact dvd_add (he 0) (he 1)

lemma coboundary_of_prime_not_dvd (p : ℕ) [hp : Fact p.Prime] [CharP K p]
    (D : MvPowerSeries (Fin 2) K) (n : ℕ) (hn : ¬p∣n)
    (hD : IsCocycle p D) (hH : D.IsHomogeneous n) :
    ∃ a : K, D=a • coboundary n := by
  let a := coeff (Finsupp.single 0 (n-1)+Finsupp.single 1 1) D/(n:K)
  have hn0 : (n:K)≠0 := (CharP.cast_eq_zero_iff K p n).not.mpr hn
  have hnat : 0<n := by
    by_contra h
    have hnz : n=0 := by omega
    exact hn (hnz ▸ dvd_zero p)
  have hsym : (D-a • coboundary n).subst ![X 1,X 0]=D-a • coboundary n := by
    have hs : HasSubst (![X 1,X 0] : Fin 2 → MvPowerSeries (Fin 2) K) :=
      hasSubst_of_constantCoeff_zero (by intro i; fin_cases i <;> simp)
    rw [subst_sub hs,subst_smul hs,hD.symmetric,coboundary_symmetric]
  have hd1 : pderiv (R := K) 1 (D-a • coboundary n)=0 := by
    rw [map_sub,Derivation.map_smul,derivative_shape p D n hnat hD hH,derivative_coboundary]
    simp only [smul_eq_C_mul,←mul_assoc,←map_mul,div_mul_cancel₀ _ hn0,sub_self,a]
  have he : D-a • coboundary n=0 := homogeneous_derivative_zero p _ n hn
    (homogeneous_sub hH (homogeneous_smul a (homogeneous_coboundary n))) (by
      intro i; fin_cases i
      · change pderiv (R := K) 0 (D-a • coboundary n)=0
        rw [derivative_symmetry _ hsym,hd1]
        rw [←coe_substAlgHom (hasSubst_of_constantCoeff_zero (by intro j; fin_cases j <;> simp)),map_zero]
      · exact hd1)
  exact ⟨a,sub_eq_zero.mp he⟩

lemma choose_pred_cast (p n : ℕ) [hp : Fact p.Prime] [CharP K p]
    (hn : 0<n) (hpn : p∣n) : ((n-1).choose (p-1) : K)=1 := by
  have hp0 : 0<p := hp.out.pos
  have hple : p≤n := Nat.le_of_dvd hn hpn
  have hmod : (n-1)%p=p-1 := by
    obtain ⟨m,rfl⟩ := hpn
    have hm : 0 < m := by nlinarith
    have hm1 : 1 ≤ m := by omega
    have heq : p*m = p*(m-1)+p := by
      nth_rw 1 [←Nat.sub_add_cancel hm1]
      ring
    have he : p*m-1=p*(m-1)+(p-1) := by omega
    simp [he,Nat.add_mod,Nat.mod_eq_of_lt (show p-1<p by omega)]
  have hh : ((n-1).choose (p-1) : K)=
      (((n-1)%p).choose ((p-1)%p)*((n-1)/p).choose ((p-1)/p) : ℕ) :=
    (CharP.natCast_eq_natCast K p).mpr Choose.choose_modEq_choose_mod_mul_choose_div_nat
  simpa [hmod,Nat.mod_eq_of_lt (show p-1<p by omega),Nat.div_eq_of_lt (show p-1<p by omega)] using hh

lemma derivative_vanish_of_large_divisible (p : ℕ) [hp : Fact p.Prime] [CharP K p]
    (D : MvPowerSeries (Fin 2) K) (n : ℕ) (hn : p<n) (hpn : p∣n)
    (hD : IsCocycle p D) (hH : D.IsHomogeneous n) : pderiv (R := K) 1 D=0 := by
  have hp1 : 1≤p := hp.out.one_le
  have hn0 : 0<n := lt_trans hp.out.pos hn
  let c := coeff (Finsupp.single 0 (n-1)+Finsupp.single 1 1) D
  have he := congrArg (coeff (Finsupp.single 0 (n-p)+Finsupp.single 1 (p-1)))
    (derivative_shape p D n hn0 hD hH)
  have hc : c=0 := by
    have hfac : ((p-1 : ℕ):K)+1=0 := by
      have hh := congrArg (fun m : ℕ => (m : K)) (Nat.sub_add_cancel hp1)
      simpa only [Nat.cast_add,Nat.cast_one,CharP.cast_eq_zero K p] using hh
    have hcho : ((n-1).choose (n-p) : K)=1 := by
      have heq : n-p=(n-1)-(p-1) := by omega
      rw [heq,Nat.choose_symm (by omega)]
      exact choose_pred_cast p n hn0 hpn
    rw [coeff_pderiv] at he
    simp only [Finsupp.add_apply,Finsupp.single_eq_same,Finsupp.single_eq_of_ne (show (1:Fin 2)≠0 by decide),zero_add,hfac,mul_zero] at he
    rw [coeff_C_mul,map_sub,coeff_add_pow _ _ _ (by omega),hcho] at he
    have hz : coeff (Finsupp.single 0 (n-p)+Finsupp.single 1 (p-1)) (X (1 : Fin 2)^(n-1) : MvPowerSeries (Fin 2) K)=0 := by
      rw [X_pow_eq,coeff_monomial,ite_eq_right]
      intro h
      have hh := congrArg (fun d : Fin 2 →₀ ℕ => d 0) h
      simp at hh
      omega
    rw [hz,sub_zero,mul_one] at he
    exact he.symm
  rw [derivative_shape p D n hn0 hD hH,show coeff _ D=c from rfl,hc,map_zero,zero_mul]

lemma prime_power_sum (p j : ℕ) [hp : Fact p.Prime] [CharP K p] (hj : j<p) :
    ∑ i ∈ Finset.range p, (i:K)^j = if j=p-1 then -1 else 0 := by
  classical
  have hz : ∑ i : ZMod p, i^j = if j=p-1 then -1 else 0 := by
    by_cases he : j=p-1
    · subst j
      simp only [ite_true]
      simp_rw [ZMod.pow_card_sub_one]
      rw [Finset.sum_ite,Finset.sum_const_zero,add_zero,Finset.sum_const,Finset.filter_ne',Finset.card_erase_of_mem (Finset.mem_univ 0)]
      simp [ZMod.card,Nat.cast_sub (show 1≤p from hp.out.one_le)]
    · rw [ite_eq_right he]
      apply FiniteField.sum_pow_lt_card_sub_one
      rw [ZMod.card]
      omega
  have hs : ∑ i ∈ Finset.range p, (i:ZMod p)^j=∑ i : ZMod p, i^j := by
    rw [←Fin.sum_univ_eq_sum_range]
    have heq (i : Fin p) : ZMod.finEquiv p i=(i.val : ZMod p) := by
      cases p with
      | zero => exact (hp.out.ne_zero rfl).elim
      | succ p =>
        apply Fin.ext
        change i.val = i.val % (p+1)
        exact (Nat.mod_eq_of_lt i.isLt).symm
    have hh := (ZMod.finEquiv p).toEquiv.sum_comp (fun x => x^j)
    change (∑ i : Fin p, (ZMod.finEquiv p i)^j)=_ at hh
    simpa only [heq] using hh
  have hh := congrArg (ZMod.castHom (dvd_refl p) K) (hs.trans hz)
  simpa only [map_sum,map_pow,map_natCast,apply_ite,map_neg,map_one,map_zero] using hh

lemma homogeneous_trace (p n : ℕ) (D : MvPowerSeries (Fin 2) K) (hH : D.IsHomogeneous n) :
    ∑ i ∈ Finset.range p, D.subst ![C (i:K)*PowerSeries.X,PowerSeries.X] =
      C (∑ j ∈ Finset.range (n+1), coeff (Finsupp.single 0 j+Finsupp.single 1 (n-j)) D *
        (∑ i ∈ Finset.range p, (i:K)^j)) * PowerSeries.X^n := by
  classical
  have hs (i : ℕ) : HasSubst (![C (i:K)*PowerSeries.X,PowerSeries.X] : Fin 2 → PowerSeries K) :=
    hasSubst_of_constantCoeff_zero (by intro a; fin_cases a <;> simp [PowerSeries.X])
  have hx : (PowerSeries.X : PowerSeries K).constantCoeff=0 := PowerSeries.constantCoeff_X
  have heach (i : ℕ) : D.subst ![C (i:K)*PowerSeries.X,PowerSeries.X]=
      ∑ j ∈ Finset.range (n+1), C (coeff (Finsupp.single 0 j+Finsupp.single 1 (n-j)) D) *
        (C (i:K)*PowerSeries.X)^j * PowerSeries.X^(n-j) := by
    conv_lhs => rw [homogeneous_sum D n hH]
    rw [←coe_substAlgHom (hs i),map_sum]
    simp only [coe_substAlgHom,subst_monomial_pair (K := K) _ _ _ (C (i:K)*PowerSeries.X) PowerSeries.X (by simp [PowerSeries.X]) hx]
  simp_rw [heach]
  simp_rw [mul_pow,←mul_assoc]
  have hterm (i j : ℕ) (hj : j∈Finset.range (n+1)) :
      C (coeff (Finsupp.single 0 j+Finsupp.single 1 (n-j)) D) * C (i:K)^j *
        PowerSeries.X^j * PowerSeries.X^(n-j)=
      C (coeff (Finsupp.single 0 j+Finsupp.single 1 (n-j)) D * (i:K)^j)*PowerSeries.X^n := by
    rw [←map_pow,←map_mul,mul_assoc,←pow_add,Nat.add_sub_of_le]
    simpa only [Finset.mem_range,Nat.lt_succ_iff] using hj
  have ht (i : ℕ) : (∑ j ∈ Finset.range (n+1), C (coeff (Finsupp.single 0 j+Finsupp.single 1 (n-j)) D) * C (i:K)^j *
        PowerSeries.X^j * PowerSeries.X^(n-j))=
      ∑ j ∈ Finset.range (n+1), C (coeff (Finsupp.single 0 j+Finsupp.single 1 (n-j)) D * (i:K)^j)*PowerSeries.X^n :=
    Finset.sum_congr rfl (fun j hj => hterm i j hj)
  simp_rw [ht]
  rw [Finset.sum_comm]
  simp only [←Finset.sum_mul,←map_sum,←Finset.mul_sum]

lemma derivative_vanish_at_prime (p : ℕ) [hp : Fact p.Prime] [CharP K p]
    (D : MvPowerSeries (Fin 2) K) (hD : IsCocycle p D) (hH : D.IsHomogeneous p) :
    pderiv (R := K) 1 D=0 := by
  classical
  have htop : coeff (Finsupp.single 0 p+Finsupp.single 1 0) D=0 := by
    have hs : HasSubst (![(X (0 : Fin 1) : MvPowerSeries (Fin 1) K),0] : Fin 2 → MvPowerSeries (Fin 1) K) :=
      hasSubst_of_constantCoeff_zero (by intro i; fin_cases i <;> simp)
    have hh := hD.zero_right
    rw [homogeneous_sum D p hH,←coe_substAlgHom hs,map_sum] at hh
    simp only [coe_substAlgHom,subst_monomial_pair (K := K) _ _ _ (X (0 : Fin 1)) 0 (constantCoeff_X _) (map_zero _)] at hh
    have hz (j : ℕ) (hj : j∈Finset.range (p+1)) (hjp : j≠p) :
        C (coeff (Finsupp.single 0 j+Finsupp.single 1 (p-j)) D) * (X (0 : Fin 1))^j * (0 : MvPowerSeries (Fin 1) K)^(p-j)=0 := by
      have he : p-j≠0 := by simp only [Finset.mem_range] at hj; omega
      rw [zero_pow he,mul_zero]
    rw [Finset.sum_eq_single p (fun j hj hne => hz j hj hne) (by simp)] at hh
    simp only [Nat.sub_self,pow_zero,mul_one] at hh
    have hc := congrArg (coeff (Finsupp.single (0 : Fin 1) p)) hh
    simpa only [coeff_C_mul,X_pow_eq,coeff_monomial_same,mul_one,map_zero] using hc
  have ht := hD.trace_zero
  rw [homogeneous_trace p p D hH] at ht
  have hsum : ∑ j ∈ Finset.range (p+1), coeff (Finsupp.single 0 j+Finsupp.single 1 (p-j)) D *
      (∑ i ∈ Finset.range p, (i:K)^j) = -coeff (Finsupp.single 0 (p-1)+Finsupp.single 1 1) D := by
    rw [Finset.sum_range_succ,Nat.sub_self,htop,zero_mul,add_zero]
    have ht : (∑ j ∈ Finset.range p, coeff (Finsupp.single 0 j+Finsupp.single 1 (p-j)) D * (∑ i ∈ Finset.range p, (i:K)^j))=
        ∑ j ∈ Finset.range p, coeff (Finsupp.single 0 j+Finsupp.single 1 (p-j)) D * (if j=p-1 then -1 else 0) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [prime_power_sum p j (Finset.mem_range.mp hj)]
    rw [ht]
    rw [Finset.sum_eq_single (p-1)]
    · simp [Nat.sub_sub_self (show 1≤p from hp.out.one_le)]
    · intro b hb hne; rw [ite_eq_right hne,mul_zero]
    · intro h; exact (h (Finset.mem_range.mpr (Nat.sub_lt hp.out.pos (by decide)))).elim
  rw [hsum] at ht
  change PowerSeries.C (-coeff (Finsupp.single 0 (p-1)+Finsupp.single 1 1) D)*PowerSeries.X^p=0 at ht
  have hc := congrArg (PowerSeries.coeff p) ht
  simp only [PowerSeries.coeff_C_mul_X_pow,map_zero,ite_true,neg_eq_zero] at hc
  rw [derivative_shape p D p hp.out.pos hD hH,hc,map_zero,zero_mul]

lemma exists_expand_of_support {σ R : Type*} [CommRing R] (f : MvPowerSeries σ R)
    (q : ℕ) (hq : q ≠ 0) (h : ∀ d, coeff d f ≠ 0 → ∀ i, q ∣ d i) :
    ∃ g, expand q hq g = f := by
  classical
  let g : MvPowerSeries σ R := fun d => coeff (q • d) f
  refine ⟨g, ?_⟩
  ext d
  by_cases hd : ∀ i, q ∣ d i
  · let e := d.mapRange (fun n => n/q) (Nat.zero_div q)
    have he : q • e = d := by
      ext i
      simp only [Finsupp.smul_apply, smul_eq_mul, e, Finsupp.mapRange_apply]
      exact Nat.mul_div_cancel' (hd i)
    rw [← he, coeff_expand_smul]
    rfl
  · obtain ⟨i, hi⟩ := not_forall.mp hd
    rw [coeff_expand_of_not_dvd _ _ _ hi]
    by_contra hf
    exact hi (h d (Ne.symm hf) i)

lemma expand_injective {R : Type*} [CommRing R] (q : ℕ) (hq : q ≠ 0) :
    Function.Injective (MvPowerSeries.expand (R := R) (σ := σ) q hq) := by
  intro f g h
  ext d
  simpa only [coeff_expand_smul] using congrArg (coeff (q • d)) h

lemma subst_expand (p : ℕ) (hp : p≠0) (D : MvPowerSeries σ K)
    (a : σ → MvPowerSeries τ K) (ha : HasSubst a) :
    (expand p hp D).subst a = D.subst (fun i => a i^p) := by
  rw [expand,substAlgHom_apply,subst_comp_subst_apply (HasSubst.X_pow hp) ha]
  congr 1
  funext i
  rw [subst_pow ha,subst_X ha]

lemma expand_subst_comm (p : ℕ) (hp : p≠0) (D : MvPowerSeries σ K)
    (a : σ → MvPowerSeries τ K) (ha : HasSubst a)
    (hpow : ∀ i, expand p hp (a i)=a i^p) :
    expand p hp (D.subst a)=(expand p hp D).subst a := by
  rw [expand_subst p hp ha,subst_expand p hp D a ha]
  congr 1
  funext i
  exact hpow i

local instance seriesCharP (p : ℕ) [CharP K p] : CharP (MvPowerSeries σ K) p :=
  charP_of_injective_ringHom MvPowerSeries.C_injective p

lemma isCocycle_of_expand (p : ℕ) [hp : Fact p.Prime] [CharP K p]
    (D : MvPowerSeries (Fin 2) K) (hD : IsCocycle p (expand p hp.out.ne_zero D)) :
    IsCocycle p D := by
  have h0 (a : Fin 2 → MvPowerSeries (Fin 1) K) (ha : HasSubst a)
      (hpow : ∀ i, expand p hp.out.ne_zero (a i)=a i^p) :
      expand p hp.out.ne_zero (D.subst a)=(expand p hp.out.ne_zero D).subst a :=
    expand_subst_comm p hp.out.ne_zero D a ha hpow
  have h3 (a : Fin 2 → MvPowerSeries (Fin 3) K) (ha : HasSubst a)
      (hpow : ∀ i, expand p hp.out.ne_zero (a i)=a i^p) :
      expand p hp.out.ne_zero (D.subst a)=(expand p hp.out.ne_zero D).subst a :=
    expand_subst_comm p hp.out.ne_zero D a ha hpow
  have hpos : p≠0 := hp.out.ne_zero
  refine ⟨?_,?_,?_,?_,?_⟩
  · apply expand_injective p hpos
    rw [map_zero,h0 _ (hasSubst_of_constantCoeff_zero (by intro i; fin_cases i <;> simp))
      (by intro i; fin_cases i <;> simp [zero_pow hpos])]
    exact hD.zero_left
  · apply expand_injective p hpos
    rw [map_zero,h0 _ (hasSubst_of_constantCoeff_zero (by intro i; fin_cases i <;> simp))
      (by intro i; fin_cases i <;> simp [zero_pow hpos])]
    exact hD.zero_right
  · apply expand_injective p hpos
    rw [expand_subst_comm p hpos D _ (hasSubst_of_constantCoeff_zero (by intro i; fin_cases i <;> simp))
      (by intro i; fin_cases i <;> simp)]
    exact hD.symmetric
  · apply expand_injective p hpos
    rw [map_add,map_add]
    rw [h3 _ (hasSubst_of_constantCoeff_zero (by intro i; fin_cases i <;> simp))
      (by intro i; fin_cases i <;> simp)]
    rw [h3 _ (hasSubst_of_constantCoeff_zero (by intro i; fin_cases i <;> simp))
      (by intro i; fin_cases i <;> simp [add_pow_char])]
    rw [h3 _ (hasSubst_of_constantCoeff_zero (by intro i; fin_cases i <;> simp))
      (by intro i; fin_cases i <;> simp)]
    rw [h3 _ (hasSubst_of_constantCoeff_zero (by intro i; fin_cases i <;> simp))
      (by intro i; fin_cases i <;> simp [add_pow_char])]
    exact hD.associative
  · apply expand_injective p hpos
    rw [map_zero,map_sum]
    have hterm (i : ℕ) : expand p hpos (D.subst ![C (i:K)*PowerSeries.X,PowerSeries.X])=
        (expand p hpos D).subst ![C (i:K)*PowerSeries.X,PowerSeries.X] := by
      apply expand_subst_comm p hpos D
      · apply hasSubst_of_constantCoeff_zero
        intro j; fin_cases j <;> simp [PowerSeries.X]
      · have hh : (i:PowerSeries K)^p=(i:PowerSeries K) := (map_natCast (frobenius (PowerSeries K) p) i)
        intro j; fin_cases j <;> simp [PowerSeries.X,map_mul,mul_pow,hh]
    simp_rw [hterm]
    exact hD.trace_zero

lemma homogeneous_of_expand (p : ℕ) (hp : p≠0) (D : MvPowerSeries (Fin 2) K)
    (n : ℕ) (hD : (expand p hp D).IsHomogeneous n) : D.IsHomogeneous (n/p) := by
  apply homogeneous_of_coeff
  intro d hd
  by_contra hn
  have hz : coeff (p • d) (expand p hp D)≠0 := by rwa [coeff_expand_smul]
  have he : (p • d).degree=n := by
    by_contra hne
    exact hz (hD.coeff_eq_zero hne)
  have hdeg : (p • d).degree=p*d.degree := by rw [map_nsmul,smul_eq_mul]
  apply hd
  rw [←he,hdeg,Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hp)]

lemma expand_coboundary (p : ℕ) [hp : Fact p.Prime] [CharP K p] (n : ℕ) :
    expand p hp.out.ne_zero (coboundary (K := K) n)=coboundary (p*n) := by
  simp only [coboundary,map_sub,map_pow,map_add,expand_X]
  rw [←add_pow_char,←pow_mul,←pow_mul,←pow_mul]

theorem cocycle_is_coboundary (p : ℕ) [hp : Fact p.Prime] [CharP K p]
    (n : ℕ) (hn : 0<n) (D : MvPowerSeries (Fin 2) K)
    (hD : IsCocycle p D) (hH : D.IsHomogeneous n) :
    ∃ a : K, D=a • coboundary n := by
  induction n using Nat.strong_induction_on generalizing D with
  | h n ih =>
    by_cases hpn : p∣n
    · have hple : p≤n := Nat.le_of_dvd hn hpn
      have hd1 : pderiv (R := K) 1 D=0 := by
        rcases hple.eq_or_lt with he | hl
        · subst n
          exact derivative_vanish_at_prime p D hD hH
        · exact derivative_vanish_of_large_divisible p D n hl hpn hD hH
      have hd : ∀ i, pderiv (R := K) i D=0 := by
        intro i; fin_cases i
        · change pderiv (R := K) 0 D=0
          rw [derivative_symmetry D hD.symmetric,hd1,
            ←coe_substAlgHom (hasSubst_of_constantCoeff_zero (by intro j; fin_cases j <;> simp)),map_zero]
        · exact hd1
      obtain ⟨E,hE⟩ := exists_expand_of_support D p hp.out.ne_zero (derivative_zero_support p D hd)
      have hEH : E.IsHomogeneous (n/p) := by
        apply homogeneous_of_expand p hp.out.ne_zero
        rwa [hE]
      have hEC : IsCocycle p E := isCocycle_of_expand p E (by rwa [hE])
      obtain ⟨a,ha⟩ := ih (n/p) (Nat.div_lt_self hn hp.out.one_lt)
        (Nat.div_pos hple hp.out.pos) E hEC hEH
      refine ⟨a,?_⟩
      rw [←hE,ha,map_smul,expand_coboundary,Nat.mul_div_cancel' hpn]
    · exact coboundary_of_prime_not_dvd p D n hpn hD hH

end HeightThree.HomogeneousCocycle

end

end OAI
