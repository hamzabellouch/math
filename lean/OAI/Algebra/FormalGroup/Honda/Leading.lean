import OAI.Algebra.FormalGroup.Honda.Jets

namespace OAI

noncomputable section

namespace HeightThree.HondaLeading
open MvPowerSeries HeightThree.HondaJets HeightThree.HomogeneousCocycle
variable {K σ : Type*} [Field K]

abbrev pair (F : FormalGroup K) (a b : MvPowerSeries σ K) := F.toPowerSeries.subst ![a,b]
lemma pair_const (F : FormalGroup K) (a b : MvPowerSeries σ K)
    (ha : a.constantCoeff=0) (hb : b.constantCoeff=0) : (pair F a b).constantCoeff=0 := by
  exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero (by
    intro i; fin_cases i <;> simp [ha,hb])) (by intro i; fin_cases i <;> simp [ha,hb]) F.zero_constantCoeff

lemma pair_linear [Finite σ] (F : FormalGroup K) (a b : MvPowerSeries σ K)
    (ha : a.constantCoeff=0) (hb : b.constantCoeff=0) : EqJet 2 (pair F a b) (a+b) := by
  have hh := law_first_order F 1 ![a,b] ![0,0]
    (by intro i; fin_cases i <;> simp [ha,hb]) (by intro i; fin_cases i <;> simp)
    (by intro i; fin_cases i
        · exact eqJet_one_zero a ha
        · exact eqJet_one_zero b hb)
  have h0 : F.toPowerSeries.subst (![0,0] : Fin 2 → MvPowerSeries σ K)=0 := by
    rw [show (![0,0] : Fin 2 → MvPowerSeries σ K)=0 by ext i; fin_cases i <;> rfl]
    exact subst_zero_of_constantCoeff_zero F.zero_constantCoeff
  simpa only [h0,sub_zero,Matrix.cons_val_zero,Matrix.cons_val_one] using hh

abbrev leading (F G : FormalGroup K) (n : ℕ) := (F.toPowerSeries-G.toPowerSeries).homogeneousComponent n

lemma leading_approx (F G : FormalGroup K) (n : ℕ)
    (h : EqJet n F.toPowerSeries G.toPowerSeries) :
    EqJet (n+1) (F.toPowerSeries-G.toPowerSeries) (leading F G n) :=
  leading_part _ n (eqJet_sub_zero.mpr h)

lemma leading_homogeneous (F G : FormalGroup K) (n : ℕ) : (leading F G n).IsHomogeneous n :=
  isHomogeneous_homogeneousComponent _ _

lemma homogeneous_zero (n : ℕ) : (0 : MvPowerSeries σ K).IsHomogeneous n := by
  apply homogeneous_of_coeff; intro d hd; simp

lemma homogeneous_C_mul (a : K) {f : MvPowerSeries σ K} {n : ℕ}
    (hf : f.IsHomogeneous n) : (C a*f).IsHomogeneous n := by
  apply homogeneous_of_coeff; intro d hd; rw [coeff_C_mul,hf.coeff_eq_zero hd,mul_zero]

lemma linear_pair_homogeneous (D : MvPowerSeries (Fin 2) K) (n : ℕ)
    (hD : D.IsHomogeneous n) (a b : MvPowerSeries σ K)
    (ha : a.constantCoeff=0) (hb : b.constantCoeff=0)
    (hHa : a.IsHomogeneous 1) (hHb : b.IsHomogeneous 1) :
    (D.subst ![a,b]).IsHomogeneous n := by
  apply homogeneous_subst_linear D n hD
  · intro i; fin_cases i <;> simp [ha,hb]
  · intro i; fin_cases i
    · exact @hHa
    · exact @hHb

lemma leading_axis (F G : FormalGroup K) (n : ℕ)
    (h : EqJet n F.toPowerSeries G.toPowerSeries) :
    (leading F G n).subst ![(0 : MvPowerSeries (Fin 1) K),X 0]=0 ∧
    (leading F G n).subst ![(X 0 : MvPowerSeries (Fin 1) K),0]=0 := by
  have hh := leading_approx F G n h
  have h0 : PowerSeries.HasSubst (X (0 : Fin 1) : MvPowerSeries (Fin 1) K) := .of_constantCoeff_zero (by simp)
  constructor
  · have hs : HasSubst (![0,X 0] : Fin 2 → MvPowerSeries (Fin 1) K) :=
      hasSubst_of_constantCoeff_zero (by intro i; fin_cases i <;> simp)
    have he := hh.subst_left _ hs (by intro i; fin_cases i <;> simp)
    rw [subst_sub hs,F.zero_add h0,G.zero_add h0,sub_self] at he
    exact homogeneous_eq_of_jet
      (linear_pair_homogeneous _ n (leading_homogeneous F G n) _ _ (by simp) (by simp)
        (homogeneous_zero 1) (homogeneous_X 0)) (homogeneous_zero n) he.symm
  · have hs : HasSubst (![X 0,0] : Fin 2 → MvPowerSeries (Fin 1) K) :=
      hasSubst_of_constantCoeff_zero (by intro i; fin_cases i <;> simp)
    have he := hh.subst_left _ hs (by intro i; fin_cases i <;> simp)
    rw [subst_sub hs,F.add_zero h0,G.add_zero h0,sub_self] at he
    exact homogeneous_eq_of_jet
      (linear_pair_homogeneous _ n (leading_homogeneous F G n) _ _ (by simp) (by simp)
        (homogeneous_X 0) (homogeneous_zero 1)) (homogeneous_zero n) he.symm

lemma leading_symmetric (F G : FormalGroup K) [F.IsComm] [G.IsComm] (n : ℕ)
    (h : EqJet n F.toPowerSeries G.toPowerSeries) :
    (leading F G n).subst ![(X 1 : MvPowerSeries (Fin 2) K),X 0]=leading F G n := by
  have hs : HasSubst (![X 1,X 0] : Fin 2 → MvPowerSeries (Fin 2) K) :=
    hasSubst_of_constantCoeff_zero (by intro i; fin_cases i <;> simp)
  have he := (leading_approx F G n h).subst_left _ hs (by intro i; fin_cases i <;> simp)
  rw [subst_sub hs,←FormalGroup.IsComm.comm,←FormalGroup.IsComm.comm] at he
  exact homogeneous_eq_of_jet
    (linear_pair_homogeneous _ n (leading_homogeneous F G n) _ _ (by simp) (by simp)
      (homogeneous_X 1) (homogeneous_X 0)) (leading_homogeneous F G n)
    (he.symm.trans (leading_approx F G n h))

lemma leading_evaluate (F G : FormalGroup K) (n : ℕ)
    (h : EqJet n F.toPowerSeries G.toPowerSeries)
    (a b u v : MvPowerSeries σ K)
    (ha : a.constantCoeff=0) (hb : b.constantCoeff=0)
    (hu : u.constantCoeff=0) (hv : v.constantCoeff=0)
    (hau : EqJet 2 a u) (hbv : EqJet 2 b v) :
    EqJet (n+1) (pair F a b-pair G a b) ((leading F G n).subst ![u,v]) := by
  have hs : HasSubst (![a,b] : Fin 2 → MvPowerSeries σ K) :=
    hasSubst_of_constantCoeff_zero (by intro i; fin_cases i <;> simp [ha,hb])
  have he := (leading_approx F G n h).subst_left _ hs (by intro i; fin_cases i <;> simp [ha,hb])
  rw [subst_sub hs] at he
  apply he.trans
  apply subst_homogeneous_leading _ n (leading_homogeneous F G n)
  · intro i; fin_cases i <;> simp [ha,hb]
  · intro i; fin_cases i <;> simp [hu,hv]
  · intro i; fin_cases i
    · exact hau
    · exact hbv

lemma leading_variation [Finite σ] (F G : FormalGroup K) (n : ℕ)
    (h : EqJet n F.toPowerSeries G.toPowerSeries)
    (a b c d u v : MvPowerSeries σ K)
    (ha : a.constantCoeff=0) (hb : b.constantCoeff=0)
    (hc : c.constantCoeff=0) (hd : d.constantCoeff=0)
    (hu : u.constantCoeff=0) (hv : v.constantCoeff=0)
    (hau : EqJet 2 a u) (hbv : EqJet 2 b v)
    (hac : EqJet n a c) (hbd : EqJet n b d) :
    EqJet (n+1) (pair F a b-pair G c d)
      ((leading F G n).subst ![u,v]+((a-c)+(b-d))) := by
  have h₁ := leading_evaluate F G n h a b u v ha hb hu hv hau hbv
  have h₂ := law_first_order G n ![a,b] ![c,d]
    (by intro i; fin_cases i <;> simp [ha,hb]) (by intro i; fin_cases i <;> simp [hc,hd])
    (by intro i; fin_cases i; exact hac; exact hbd)
  convert h₁.add h₂ using 1
  · dsimp only [pair]; ring
  · rfl

lemma leading_associative (F G : FormalGroup K) (n : ℕ)
    (h : EqJet n F.toPowerSeries G.toPowerSeries) :
    (leading F G n).subst ![(X 0 : MvPowerSeries (Fin 3) K),X 1] +
      (leading F G n).subst ![(X 0+X 1 : MvPowerSeries (Fin 3) K),X 2] =
    (leading F G n).subst ![(X 1 : MvPowerSeries (Fin 3) K),X 2] +
      (leading F G n).subst ![(X 0 : MvPowerSeries (Fin 3) K),X 1+X 2] := by
  let x : MvPowerSeries (Fin 3) K := X 0
  let y : MvPowerSeries (Fin 3) K := X 1
  let z : MvPowerSeries (Fin 3) K := X 2
  have hx : x.constantCoeff=0 := by simp [x]
  have hy : y.constantCoeff=0 := by simp [y]
  have hz : z.constantCoeff=0 := by simp [z]
  have hxy : EqJet n (pair F x y) (pair G x y) :=
    h.subst_left _ (hasSubst_of_constantCoeff_zero (by intro i; fin_cases i <;> simp [hx,hy]))
      (by intro i; fin_cases i <;> simp [hx,hy])
  have hyz : EqJet n (pair F y z) (pair G y z) :=
    h.subst_left _ (hasSubst_of_constantCoeff_zero (by intro i; fin_cases i <;> simp [hy,hz]))
      (by intro i; fin_cases i <;> simp [hy,hz])
  have hL := leading_variation F G n h (pair F x y) z (pair G x y) z (x+y) z
    (pair_const F x y hx hy) hz (pair_const G x y hx hy) hz (by simp [hx,hy]) hz
    (pair_linear F x y hx hy) (EqJet.refl 2 z) hxy (EqJet.refl n z)
  have hE₁ := leading_evaluate F G n h x y x y hx hy hx hy (EqJet.refl 2 x) (EqJet.refl 2 y)
  have hL' : EqJet (n+1) (pair F (pair F x y) z-pair G (pair G x y) z)
      ((leading F G n).subst ![x+y,z]+(leading F G n).subst ![x,y]) := by
    refine EqJet.trans ?_ ((EqJet.refl _ _).add hE₁)
    simpa only [sub_self,add_zero] using hL
  have hR := leading_variation F G n h x (pair F y z) x (pair G y z) x (y+z)
    hx (pair_const F y z hy hz) hx (pair_const G y z hy hz) hx (by simp [hy,hz])
    (EqJet.refl 2 x) (pair_linear F y z hy hz) (EqJet.refl n x) hyz
  have hE₂ := leading_evaluate F G n h y z y z hy hz hy hz (EqJet.refl 2 y) (EqJet.refl 2 z)
  have hR' : EqJet (n+1) (pair F x (pair F y z)-pair G x (pair G y z))
      ((leading F G n).subst ![x,y+z]+(leading F G n).subst ![y,z]) := by
    refine EqJet.trans ?_ ((EqJet.refl _ _).add hE₂)
    simpa only [sub_self,zero_add] using hR
  have heq : pair F (pair F x y) z-pair G (pair G x y) z=
      pair F x (pair F y z)-pair G x (pair G y z) := by
    rw [pair,F.assoc' (.of_constantCoeff_zero hx) (.of_constantCoeff_zero hy) (.of_constantCoeff_zero hz)]
    rw [pair,G.assoc' (.of_constantCoeff_zero hx) (.of_constantCoeff_zero hy) (.of_constantCoeff_zero hz)]
  rw [heq] at hL'
  have hlin (a b : MvPowerSeries (Fin 3) K) (ha : a.constantCoeff=0) (hb : b.constantCoeff=0)
      (haH : a.IsHomogeneous 1) (hbH : b.IsHomogeneous 1) :
      ((leading F G n).subst ![a,b]).IsHomogeneous n := by
    exact linear_pair_homogeneous _ n (leading_homogeneous F G n) a b ha hb haH hbH
  have hxH : x.IsHomogeneous 1 := by exact homogeneous_X 0
  have hyH : y.IsHomogeneous 1 := by exact homogeneous_X 1
  have hzH : z.IsHomogeneous 1 := by exact homogeneous_X 2
  have hsumxy : (x+y).IsHomogeneous 1 := by exact hxH.add hyH
  have hsumyz : (y+z).IsHomogeneous 1 := by exact hyH.add hzH
  have hleft : ((leading F G n).subst ![x+y,z]+(leading F G n).subst ![x,y]).IsHomogeneous n := by
    apply MvPowerSeries.IsHomogeneous.add
    · exact hlin _ _ (by simp [hx,hy]) hz hsumxy hzH
    · exact hlin _ _ hx hy hxH hyH
  have hright : ((leading F G n).subst ![x,y+z]+(leading F G n).subst ![y,z]).IsHomogeneous n := by
    apply MvPowerSeries.IsHomogeneous.add
    · exact hlin _ _ hx (by simp [hy,hz]) hxH hsumyz
    · exact hlin _ _ hy hz hyH hzH
  simpa only [add_comm] using homogeneous_eq_of_jet hleft hright (hL'.symm.trans hR')

end HeightThree.HondaLeading

namespace HeightThree.HondaLeading
open MvPowerSeries HeightThree.HondaJets HeightThree.HomogeneousCocycle HeightThree.HondaTarget
variable {K : Type*} [Field K]

@[simp] lemma multiplication_zero (F : FormalGroup K) : multiplicationSeries F 0=0 := rfl
lemma multiplication_succ (F : FormalGroup K) (n : ℕ) :
    multiplicationSeries F (n+1) = pair F (multiplicationSeries F n) PowerSeries.X := by
  change ((n+1) • variablePoint F).val = _
  rw [succ_nsmul]
  rfl
@[simp] lemma multiplication_constant (F : FormalGroup K) (n : ℕ) :
    MvPowerSeries.constantCoeff (multiplicationSeries F n)=0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [multiplication_succ]
    exact pair_const F _ _ ih (by simp [PowerSeries.X])

lemma multiplication_linear (F : FormalGroup K) (i : ℕ) :
    EqJet 2 (multiplicationSeries F i) (C (i:K)*PowerSeries.X) := by
  induction i with
  | zero => simpa using (EqJet.refl 2 (0 : PowerSeries K))
  | succ i ih =>
    rw [multiplication_succ]
    have hh := pair_linear F (multiplicationSeries F i) PowerSeries.X
      (by exact multiplication_constant F i) (by simp [PowerSeries.X])
    have hh' := hh.trans (ih.add (EqJet.refl _ PowerSeries.X))
    convert hh' using 1
    simp only [Nat.cast_add,Nat.cast_one,map_add,map_one,add_mul,one_mul]

lemma multiplication_match (F G : FormalGroup K) (n : ℕ)
    (h : EqJet n F.toPowerSeries G.toPowerSeries) (i : ℕ) :
    EqJet n (multiplicationSeries F i) (multiplicationSeries G i) := by
  induction i with
  | zero => exact EqJet.refl _ _
  | succ i ih =>
    rw [multiplication_succ,multiplication_succ]
    have h₁ := h.subst_left ![multiplicationSeries F i,PowerSeries.X]
      (hasSubst_of_constantCoeff_zero (by intro j; fin_cases j <;> simp [multiplication_constant,PowerSeries.X]))
      (by intro j; fin_cases j <;> simp [multiplication_constant,PowerSeries.X])
    apply h₁.trans
    apply EqJet.subst_right G.toPowerSeries
    · exact hasSubst_of_constantCoeff_zero (by intro j; fin_cases j <;> simp [multiplication_constant,PowerSeries.X])
    · exact hasSubst_of_constantCoeff_zero (by intro j; fin_cases j <;> simp [multiplication_constant,PowerSeries.X])
    · intro j; fin_cases j
      · exact ih
      · exact EqJet.refl _ _

lemma multiplication_leading_trace (F G : FormalGroup K) (n : ℕ)
    (h : EqJet n F.toPowerSeries G.toPowerSeries) (i : ℕ) :
    EqJet (n+1) (multiplicationSeries F i-multiplicationSeries G i)
      (∑j∈Finset.range i, (leading F G n).subst ![C (j:K)*PowerSeries.X,PowerSeries.X]) := by
  induction i with
  | zero => simpa using (EqJet.refl (n+1) (0 : PowerSeries K))
  | succ i ih =>
    rw [multiplication_succ,multiplication_succ,Finset.sum_range_succ]
    have hh := leading_variation F G n h (multiplicationSeries F i) PowerSeries.X
      (multiplicationSeries G i) PowerSeries.X (C (i:K)*PowerSeries.X) PowerSeries.X
      (multiplication_constant F i) (by simp [PowerSeries.X])
      (multiplication_constant G i) (by simp [PowerSeries.X])
      (by simp [PowerSeries.X]) (by simp [PowerSeries.X])
      (multiplication_linear F i) (EqJet.refl _ _) (multiplication_match F G n h i) (EqJet.refl _ _)
    have hh₁ : EqJet (n+1)
        (pair F (multiplicationSeries F i) PowerSeries.X-pair G (multiplicationSeries G i) PowerSeries.X)
        ((leading F G n).subst ![C (i:K)*PowerSeries.X,PowerSeries.X]+
          (multiplicationSeries F i-multiplicationSeries G i)) := by
      simpa only [sub_self,add_zero] using hh
    have hh₂ := hh₁.trans ((EqJet.refl _ _).add ih)
    simpa only [add_comm] using hh₂

lemma homogeneous_sum {σ ι : Type*} (s : Finset ι) (f : ι → MvPowerSeries σ K) (n : ℕ)
    (hf : ∀ i∈s,(f i).IsHomogeneous n) : (∑i∈s,f i).IsHomogeneous n := by
  apply homogeneous_of_coeff
  intro d hd; rw [map_sum]; apply Finset.sum_eq_zero
  intro i hi
  have hh : (f i).IsHomogeneous n := by exact hf i hi
  exact hh.coeff_eq_zero hd

lemma leading_trace_zero (F G : FormalGroup K) (n p : ℕ)
    (h : EqJet n F.toPowerSeries G.toPowerSeries)
    (hp : multiplicationSeries F p=multiplicationSeries G p) :
    (∑i∈Finset.range p, (leading F G n).subst ![C (i:K)*PowerSeries.X,PowerSeries.X])=0 := by
  have hh := multiplication_leading_trace F G n h p
  rw [hp,sub_self] at hh
  apply homogeneous_eq_of_jet _ (homogeneous_zero n) hh.symm
  apply homogeneous_sum
  intro i hi
  apply linear_pair_homogeneous _ n (leading_homogeneous F G n)
  · simp [PowerSeries.X]
  · simp [PowerSeries.X]
  · exact homogeneous_C_mul _ (homogeneous_X ())
  · exact homogeneous_X ()

theorem leading_isCocycle (F G : FormalGroup K) [F.IsComm] [G.IsComm] (n p : ℕ)
    (h : EqJet n F.toPowerSeries G.toPowerSeries)
    (hp : multiplicationSeries F p=multiplicationSeries G p) :
    IsCocycle p (leading F G n) :=
  ⟨(leading_axis F G n h).1,(leading_axis F G n h).2,leading_symmetric F G n h,
    leading_associative F G n h,leading_trace_zero F G n p h hp⟩

end HeightThree.HondaLeading

end

end OAI
