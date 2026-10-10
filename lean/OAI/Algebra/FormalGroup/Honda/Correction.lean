import OAI.Algebra.FormalGroup.Honda.Frobenius

namespace OAI

noncomputable section

namespace HeightThree.HondaCorrection
open MvPowerSeries HeightThree.HondaJets HeightThree.HondaLeading
open HeightThree.HondaTarget HeightThree.HondaFrobenius HeightThree.HomogeneousCocycle
open HeightThree.CoordinateTransport HeightThree.DeformationRigidity
variable {K σ : Type*} [Field K]

def stepSeries (n : ℕ) (a : K) : PowerSeries K := PowerSeries.X+PowerSeries.C a*PowerSeries.X^n

lemma step_zero (n : ℕ) (hn : 0<n) (a : K) : (stepSeries n a).constantCoeff=0 := by
  simp [stepSeries,hn.ne']
lemma step_linear (n : ℕ) (hn : 2≤n) (a : K) : (stepSeries n a).coeff 1=1 := by
  simp [stepSeries,map_add,PowerSeries.coeff_C_mul,PowerSeries.coeff_X_pow,show 1≠n by omega]

def step (n : ℕ) (hn : 2≤n) (a : K) : Coordinate K :=
  Coordinate.ofSeries (stepSeries n a) (step_zero n (by omega) a) (by rw [step_linear n hn a]; exact isUnit_one)

lemma step_subst (n : ℕ) (a : K) (z : MvPowerSeries σ K) (hz : z.constantCoeff=0) :
    (stepSeries n a).subst z=z+C a*z^n := by
  have hs : PowerSeries.HasSubst z := .of_constantCoeff_zero hz
  simp [stepSeries,PowerSeries.subst_add hs,PowerSeries.subst_mul hs,PowerSeries.subst_pow hs,
    PowerSeries.subst_X hs,PowerSeries.subst_C]

lemma step_jet (n : ℕ) (a : K) (z : MvPowerSeries σ K) (hz : z.constantCoeff=0) :
    EqJet n ((stepSeries n a).subst z) z := by
  rw [step_subst n a z hz]
  have hh := (eqJet_pow_zero z hz n).mul_left (C a)
  simpa using (EqJet.refl n z).add hh

lemma step_Xjet (n : ℕ) (_ : 0<n) (a : K) : EqJet n (stepSeries n a) PowerSeries.X := by
  have hh := step_jet n a (PowerSeries.X : PowerSeries K) (by simp [PowerSeries.X])
  simpa only [PowerSeries.X_subst] using hh

lemma pullback_step_jet (c : Coordinate K) (F G : FormalGroup K) (m : ℕ)
    (h : EqJet m (c.series.subst G.toPowerSeries)
      (F.toPowerSeries.subst ![c.series.subst (X 0),c.series.subst (X 1)])) :
    EqJet m (c.transport G).toPowerSeries F.toPowerSeries := by
  let b : Fin 2 → MvPowerSeries (Fin 2) K := ![c.inverse.subst (X 0),c.inverse.subst (X 1)]
  have hb0 : ∀i,(b i).constantCoeff=0 := by
    intro i; fin_cases i <;> exact c.inverse_const _ (by simp)
  have hb := hasSubst_of_constantCoeff_zero hb0
  have ha : HasSubst ![c.series.subst (X 0 : MvPowerSeries (Fin 2) K),c.series.subst (X 1)] :=
    hasSubst_of_constantCoeff_zero (by intro i; fin_cases i <;> exact c.series_const _ (by simp))
  have hh := h.subst_left b hb hb0
  rw [subst_after_mv _ _ (.of_constantCoeff_zero G.zero_constantCoeff) _ hb,
    MvPowerSeries.subst_comp_subst_apply ha hb] at hh
  have he : (fun i : Fin 2=>
      (![c.series.subst (X 0 : MvPowerSeries (Fin 2) K),c.series.subst (X 1)] i).subst b)=X := by
    funext i; fin_cases i
    · change (c.series.subst (X 0 : MvPowerSeries (Fin 2) K)).subst b=X 0
      rw [subst_after_mv _ _ (PowerSeries.HasSubst.X _) _ hb,subst_X hb]
      exact c.series_inverse _ (PowerSeries.HasSubst.X _)
    · change (c.series.subst (X 1 : MvPowerSeries (Fin 2) K)).subst b=X 1
      rw [subst_after_mv _ _ (PowerSeries.HasSubst.X _) _ hb,subst_X hb]
      exact c.series_inverse _ (PowerSeries.HasSubst.X _)
  rw [he,subst_self] at hh
  exact hh

lemma step_improves (F G : FormalGroup K) (n : ℕ) (hn : 2≤n)
    (h : EqJet n F.toPowerSeries G.toPowerSeries) (a : K)
    (ha : leading F G n=a • coboundary n) :
    EqJet (n+1) ((step n hn a).transport G).toPowerSeries F.toPowerSeries := by
  apply pullback_step_jet
  change EqJet _ ((stepSeries n a).subst G.toPowerSeries)
    (F.toPowerSeries.subst ![(stepSeries n a).subst (X 0),(stepSeries n a).subst (X 1)])
  let b : Fin 2 → MvPowerSeries (Fin 2) K := ![(stepSeries n a).subst (X 0),(stepSeries n a).subst (X 1)]
  have hb0 : ∀i,(b i).constantCoeff=0 := by
    intro i; fin_cases i <;> exact (step n hn a).series_const _ (by simp)
  have hbx : ∀i,EqJet n (b i) (X i) := by
    intro i; fin_cases i <;> exact step_jet n a _ (by simp)
  have hinner := law_first_order F n b X hb0 (by simp) hbx
  rw [subst_self] at hinner
  have hlin : EqJet 2 G.toPowerSeries (X 0+X 1) := by
    simpa only [pair_subst_self] using pair_linear G (X 0 : MvPowerSeries (Fin 2) K) (X 1) (by simp) (by simp)
  have hpow := (hlin.pow_leading G.zero_constantCoeff (by simp) n).mul_left (C a)
  have hout := (EqJet.refl (n+1) G.toPowerSeries).add hpow
  rw [←step_subst n a _ G.zero_constantCoeff] at hout
  have hlead := leading_approx F G n h
  rw [ha] at hlead
  intro d hd
  have hi := hinner d hd
  have ho := hout d hd
  have hl := hlead d hd
  simp only [b,Matrix.cons_val_zero,Matrix.cons_val_one,step_subst n a _ (constantCoeff_X _),
    add_sub_cancel_left,map_add,map_sub] at hi
  simp only [coboundary,smul_eq_C_mul,mul_sub,map_sub] at hl
  simp only [map_add] at ho
  change coeff d ((stepSeries n a).subst G.toPowerSeries)=coeff d (F.toPowerSeries.subst b)
  simp only [id_eq] at hi
  simp only [b,step_subst n a _ (constantCoeff_X _)]
  linear_combination ho-hi-hl

end HeightThree.HondaCorrection

namespace HeightThree.HondaCorrection
open MvPowerSeries HeightThree.HondaJets HeightThree.HondaLeading
open HeightThree.HondaTarget HeightThree.HondaFrobenius HeightThree.HomogeneousCocycle
open HeightThree.CoordinateTransport HeightThree.DeformationRigidity
variable {K : Type*} [Field K]

lemma step_commutes (p : ℕ) [hp : Fact p.Prime] [CharP K p]
    (h n : ℕ) (hn : 0<n) (a : K) (ha : (iterateFrobenius K p h) a=a) :
    (stepSeries n a).subst (PowerSeries.X^(p^h) : PowerSeries K)=
      (PowerSeries.X^(p^h) : PowerSeries K).subst (stepSeries n a) := by
  let : CharP (PowerSeries K) p := charP_of_injective_ringHom PowerSeries.C_injective p
  have hq : p^h≠0 := pow_ne_zero _ hp.out.ne_zero
  have hqa : a^(p^h)=a := ha
  rw [step_subst n a _ (by simp [PowerSeries.X,hp.out.ne_zero]),PowerSeries.subst_pow (.of_constantCoeff_zero (step_zero n hn a))]
  rw [PowerSeries.subst_X (.of_constantCoeff_zero (step_zero n hn a))]
  rw [stepSeries,add_pow_char_pow,mul_pow,←map_pow,hqa]
  change PowerSeries.X^(p^h)+PowerSeries.C a*(PowerSeries.X^(p^h))^n=
    PowerSeries.X^(p^h)+PowerSeries.C a*(PowerSeries.X^n)^(p^h)
  simp only [←pow_mul,Nat.mul_comm]

lemma honda_transport (p : ℕ) [hp : Fact p.Prime] [CharP K p]
    (h n : ℕ) (hn : 2≤n) (a : K) (ha : (iterateFrobenius K p h) a=a)
    (G : FormalGroup K) (hG : multiplicationSeries G p=PowerSeries.X^(p^h)) :
    multiplicationSeries ((step n hn a).transport G) p=PowerSeries.X^(p^h) := by
  let c := step n hn a
  have hh := coordinate_multiplication G (c.transport G) (c.iso G) p
  change c.series.subst (multiplicationSeries G p)=(multiplicationSeries (c.transport G) p).subst c.series at hh
  rw [hG] at hh
  have he := step_commutes p h n (by omega) a ha
  rw [show c.series=stepSeries n a from rfl,he] at hh
  change (PowerSeries.X^(p^h) : PowerSeries K).subst c.series=(multiplicationSeries (c.transport G) p).subst c.series at hh
  have hz := congrArg (fun f : PowerSeries K=>f.subst c.inverse) hh
  rw [PowerSeries.subst_comp_subst_apply c.hasSubst c.inv_hasSubst,
    PowerSeries.subst_comp_subst_apply c.hasSubst c.inv_hasSubst,c.left_inv,
    PowerSeries.X_subst,PowerSeries.X_subst] at hz
  exact hz.symm

end HeightThree.HondaCorrection

end

end OAI
