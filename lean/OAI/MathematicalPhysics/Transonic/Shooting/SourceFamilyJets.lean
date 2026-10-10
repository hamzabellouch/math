import OAI.MathematicalPhysics.Transonic.Shooting.ContinuousJets

namespace OAI

section
noncomputable section

namespace SepticProfile.SourceFamily
open Set Polynomial ParametricJets
open ShootingParameters
abbrev Parameter := ↥(Icc leftEnd rightEnd)

lemma continuous_a : Continuous (fun t : Parameter => a t.val) := by unfold a;fun_prop
lemma continuous_e : Continuous (fun t : Parameter => e t.val) := by unfold e;fun_prop
lemma continuous_d : Continuous (fun t : Parameter => d t.val) := by unfold d;fun_prop
lemma continuous_k : Continuous (fun t : Parameter => k t.val) := by unfold k;fun_prop

lemma continuous_sigma : Continuous (fun t : Parameter => sigma t.val) := by
  apply Continuous.div
  · exact continuous_const.mul (continuous_d.pow 2)
  · exact continuous_const.mul (continuous_e.pow 2)
  · intro t
    exact ne_of_gt (mul_pos (by norm_num) (sq_pos_of_pos (e_pos t.property)))
lemma continuous_kappa : Continuous (fun t : Parameter => kappa t.val) := by
  apply Continuous.div
  · fun_prop
  · exact continuous_const.mul continuous_e
  · intro t
    exact ne_of_gt (mul_pos (by norm_num) (e_pos t.property))
lemma continuous_slope : Continuous (fun t : Parameter => slope t.val) := by
  apply Continuous.div continuous_e (continuous_const.mul continuous_a)
  intro t
  exact ne_of_gt (mul_pos (by norm_num) (a_pos t.property))
lemma continuous_ratio : Continuous (fun t : Parameter => ratio t.val) := by
  exact (continuous_const.mul continuous_a).div continuous_k (fun t => ne_of_gt (k_pos t.property))

def sig : C(Parameter,ℝ) := ⟨fun t => sigma t.val,continuous_sigma⟩
def kap : C(Parameter,ℝ) := ⟨fun t => kappa t.val,continuous_kappa⟩
def slp : C(Parameter,ℝ) := ⟨fun t => slope t.val,continuous_slope⟩
def rho : C(Parameter,ℝ) := ⟨fun t => ratio t.val,continuous_ratio⟩
def cst : C(Parameter,ℝ) := ContinuousMap.const _ (3/5:ℝ)

structure FamilyJet where
  p : Polynomial C(Parameter,ℝ)
  p1 : Polynomial C(Parameter,ℝ)
  S : Polynomial C(Parameter,ℝ)
  E : Polynomial C(Parameter,ℝ)
  p_zero : p.coeff 0=1
  p_one : p.coeff 1=slp
  p_split : p=1+X*p1
  p1_zero : p1.coeff 0=slp
  residual : ParametricJets.residualP sig kap cst p=X^77*S
  linearization : C rho*ParametricJets.denQuotP sig p1+
    ParametricJets.linP sig kap cst p=X*E

/-- One continuous finite jet of order76 works on the whole chart. In
particular this is not a separate choice of polynomial at every parameter. -/
theorem exists_familyJet : Nonempty FamilyJet := by
  obtain ⟨p,p1,S,E,hp0,hp1,hp,hp10,hr,hlin⟩ :=
    ParametricJets.exists_continuous_jet sig kap cst slp rho
      (fun t => sonic_quadratic t.property) (fun t => sonic_divisor_ne t.property)
      (fun t => ratio_identity t.property) (fun t => nonresonance t.property) 74
  exact ⟨⟨p,p1,S,E,hp0,hp1,hp,hp10,hr,hlin⟩⟩

lemma indicial_shift (t : Parameter) : 2 < 76-rho t := by
  have h := (ratio_bounds t.property).2
  change ratio t.val < 74 at h
  change 2 < 76-ratio t.val
  linarith

lemma specialize_prefP (a : Parameter) (sigma : C(Parameter,ℝ)) :
    ParametricJets.specialize a (ParametricJets.prefP sigma)=SourceSonic.prefP (sigma a) := by
  simp [ParametricJets.prefP,SourceSonic.prefP,ParametricJets.specialize]
lemma specialize_denQuotP (a : Parameter) (sigma : C(Parameter,ℝ)) (p : Polynomial C(Parameter,ℝ)) :
    ParametricJets.specialize a (ParametricJets.denQuotP sigma p)=
      SourceSonic.denQuotP (sigma a) (ParametricJets.specialize a p) := by
  simp only [ParametricJets.denQuotP,SourceSonic.denQuotP,map_mul,map_sub,map_neg,
    map_pow,map_ofNat,specialize_prefP]
  simp [ParametricJets.specialize]
lemma specialize_transP (a : Parameter) (kappa : C(Parameter,ℝ)) (p : Polynomial C(Parameter,ℝ)) :
    ParametricJets.specialize a (ParametricJets.transP kappa p)=
      SourceSonic.transP (kappa a) (ParametricJets.specialize a p) := by
  simp [ParametricJets.transP,SourceSonic.transP,ParametricJets.specialize]
lemma specialize_linP (a : Parameter) (sigma kappa c : C(Parameter,ℝ)) (p : Polynomial C(Parameter,ℝ)) :
    ParametricJets.specialize a (ParametricJets.linP sigma kappa c p)=
      SourceSonic.linP (sigma a) (kappa a) (c a) (ParametricJets.specialize a p) := by
  simp only [ParametricJets.linP,SourceSonic.linP,map_add,map_mul,map_sub,map_pow,map_neg,
    map_ofNat,map_one,specialize_C,specialize_derivative,specialize_transP,specialize_prefP]
  simp [ParametricJets.specialize]

end SepticProfile.SourceFamily

end
end

end OAI
