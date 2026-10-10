import Mathlib
import OAI.MathematicalPhysics.BFSS.DistanceBounds

namespace OAI

/-! Compact gauge orbits, stabilizers and equivariant normal slices. -/

namespace BFSSOrbit
noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator
lemma unitary_compact {N : ℕ} (hN : 2 ≤ N) :
    IsCompact (unitary (Matrix (Fin N) (Fin N) ℂ) : Set (Matrix (Fin N) (Fin N) ℂ)) := by
  let : NeZero N := ⟨by omega⟩
  apply (isCompact_closedBall (0 : Matrix (Fin N) (Fin N) ℂ) 1).of_isClosed_subset isClosed_unitary
  intro U hU
  rw [Metric.mem_closedBall,dist_zero_right,CStarRing.norm_of_mem_unitary hU]
end
end BFSSOrbit
namespace BFSSQuantum.AlgebraData
noncomputable section
open Matrix Finset Set
open scoped Matrix.Norms.L2Operator
variable {N : ℕ} (M : AlgebraData N)

lemma colorConjugate_one (a : ColorVector N) : M.colorConjugate 1 a = a := by
  change M.colorExtract (1 * M.colorEmbed a * (1:ColorMatrix N)ᴴ) = a
  simp only [Matrix.conjTranspose_one,one_mul,mul_one,M.colorExtract_embed]

lemma colorConjugate_mul (U V : ColorMatrix N) (hV : V ∈ unitary (ColorMatrix N))
    (a : ColorVector N) : M.colorConjugate (U*V) a = M.colorConjugate U (M.colorConjugate V a) := by
  change M.colorExtract ((U*V)*M.colorEmbed a*(U*V)ᴴ) =
    M.colorExtract (U*M.colorEmbed (M.colorConjugate V a)*Uᴴ)
  rw [M.colorEmbed_conjugate V hV,Matrix.conjTranspose_mul]
  simp only [mul_assoc]

lemma gaugeConjugate_one (q : Boson N) : M.gaugeConjugate 1 q = q := by
  ext p
  change M.colorConjugate 1 (spatialColor q p.1) p.2 = q p
  rw [M.colorConjugate_one]
  rfl

lemma gaugeConjugate_mul (U V : ColorMatrix N) (hV : V ∈ unitary (ColorMatrix N))
    (q : Boson N) : M.gaugeConjugate (U*V) q = M.gaugeConjugate U (M.gaugeConjugate V q) := by
  ext p
  change M.colorConjugate (U*V) (spatialColor q p.1) p.2 =
    M.colorConjugate U (spatialColor (M.gaugeConjugate V q) p.1) p.2
  rw [M.spatialColor_gaugeConjugate,M.colorConjugate_mul U V hV]

lemma gaugeConjugate_continuous (q : Boson N) : Continuous (fun U => M.gaugeConjugate U q) := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro p
  change Continuous (fun U : ColorMatrix N => M.colorExtract (U*M.colorEmbed (spatialColor q p.1)*Uᴴ) p.2)
  exact (PiLp.continuous_apply 2 _ p.2).comp
    (M.colorExtract.toContinuousLinearMap.continuous.comp ((continuous_id.mul continuous_const).mul continuous_star))

def gaugeOrbit (q : Boson N) : Set (Boson N) :=
  (fun U => M.gaugeConjugate U q) '' (unitary (ColorMatrix N) : Set (ColorMatrix N))

lemma self_mem_gaugeOrbit (q : Boson N) : q ∈ M.gaugeOrbit q :=
  ⟨1,OneMemClass.one_mem _,M.gaugeConjugate_one q⟩

lemma gaugeOrbit_isCompact (hN : 2 ≤ N) (q : Boson N) : IsCompact (M.gaugeOrbit q) :=
  (BFSSOrbit.unitary_compact hN).image (M.gaugeConjugate_continuous q)

lemma gaugeOrbit_subset_massiveZeros (q : Boson N) (hq : q ∈ M.massiveZeros) :
    M.gaugeOrbit q ⊆ M.massiveZeros := by
  rintro p ⟨U,hU,rfl⟩
  exact M.gaugeConjugate_mem_massiveZeros U hU q hq

lemma gaugeOrbit_invariant (q p : Boson N) (hp : p ∈ M.gaugeOrbit q)
    (V : ColorMatrix N) (hV : V ∈ unitary (ColorMatrix N)) :
    M.gaugeConjugate V p ∈ M.gaugeOrbit q := by
  rcases hp with ⟨U,hU,rfl⟩
  exact ⟨V*U,mul_mem hV hU,M.gaugeConjugate_mul V U hU q⟩

lemma gaugeCurve_mem_gaugeOrbit (q p : Boson N) (hp : p ∈ M.gaugeOrbit q)
    (w : ColorVector N) (t : ℝ) : M.gaugeCurve p w t ∈ M.gaugeOrbit q :=
  M.gaugeOrbit_invariant q p hp _
    (BFSSGaugeFlow.exp_skew _ (M.colorCombination_hermitian w) t)

lemma nearest_gaugeOrbit_normal (x q p : Boson N) (hp : p ∈ M.gaugeOrbit q)
    (hmin : ∀ z ∈ M.gaugeOrbit q, ‖x-p‖ ≤ ‖x-z‖) : x-p ∈ M.normalSlice p := by
  rw [normalSlice,Submodule.mem_orthogonal']
  intro u hu
  obtain ⟨w,rfl⟩ := hu
  have hd := ((hasDerivAt_const (0:ℝ) x).sub (M.gaugeCurve_deriv_zero p w)).norm_sq
  have hm : IsLocalMin (fun t : ℝ => ‖x-M.gaugeCurve p w t‖^2) 0 := by
    apply Filter.Eventually.of_forall
    intro t
    change ‖x-M.gaugeCurve p w 0‖^2 ≤ ‖x-M.gaugeCurve p w t‖^2
    rw [M.gaugeCurve_zero]
    exact sq_le_sq₀ (norm_nonneg _) (norm_nonneg _) |>.mpr
      (hmin _ (M.gaugeCurve_mem_gaugeOrbit q p hp w t))
  have he := hm.hasDerivAt_eq_zero hd
  simp only [Pi.sub_apply,M.gaugeCurve_zero,zero_sub,inner_neg_right] at he
  linarith

lemma nearest_gaugeOrbit (hN : 2 ≤ N) (x q : Boson N) :
    ∃ p ∈ M.gaugeOrbit q, ‖x-p‖ = Metric.infDist x (M.gaugeOrbit q) ∧
      x-p ∈ M.normalSlice p := by
  obtain ⟨p,hp,he⟩ := (M.gaugeOrbit_isCompact hN q).exists_infDist_eq_dist
    ⟨q,M.self_mem_gaugeOrbit q⟩ x
  have he' : ‖x-p‖ = Metric.infDist x (M.gaugeOrbit q) := by
    simpa only [dist_eq_norm] using he.symm
  refine ⟨p,hp,he',M.nearest_gaugeOrbit_normal x q p hp ?_⟩
  intro z hz
  rw [he']
  simpa only [dist_eq_norm] using Metric.infDist_le_dist_of_mem (x := x) hz

theorem massiveZeros_locally_single_orbit (hN : 2 ≤ N) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ q ∈ M.massiveZeros, ∀ x ∈ M.massiveZeros,
      ‖x-q‖ ≤ δ → x ∈ M.gaugeOrbit q := by
  obtain ⟨c,δ,hc,hδ,hlower⟩ := M.potential_uniform_normal_lower hN
  refine ⟨δ,hδ,?_⟩
  intro q hq x hx hclose
  obtain ⟨p,hp,he,hn⟩ := M.nearest_gaugeOrbit hN x q
  have hb : ‖x-p‖ ≤ ‖x-q‖ := by
    rw [he]
    simpa only [dist_eq_norm] using
      Metric.infDist_le_dist_of_mem (x := x) (M.self_mem_gaugeOrbit q)
  have hh := hlower p (M.gaugeOrbit_subset_massiveZeros q hq hp) (x-p) hn (hb.trans hclose)
  rw [add_sub_cancel] at hh
  change M.deformedBosonicPotential 1 1 x = 0 at hx
  rw [hx] at hh
  have hz : x-p = 0 := by
    apply norm_eq_zero.mp
    have hs : ‖x-p‖^2 ≤ 0 := nonpos_of_mul_nonpos_right hh hc
    nlinarith [norm_nonneg (x-p)]
  exact (sub_eq_zero.mp hz) ▸ hp

theorem massiveZeros_finite_orbits (hN : 2 ≤ N) :
    ∃ S : Set (Boson N), S.Finite ∧ S ⊆ M.massiveZeros ∧
      M.massiveZeros = ⋃ q ∈ S, M.gaugeOrbit q := by
  obtain ⟨δ,hδ,horbit⟩ := M.massiveZeros_locally_single_orbit hN
  obtain ⟨S,hS,hfin,hcover⟩ := (M.massiveZeros_isCompact hN).finite_cover_balls hδ
  refine ⟨S,hfin,hS,?_⟩
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨q,hq,hball⟩ := Set.mem_iUnion₂.mp (hcover hx)
    apply Set.mem_iUnion₂.mpr
    exact ⟨q,hq,horbit q (hS hq) x hx (le_of_lt (by simpa only [Metric.mem_ball,dist_eq_norm] using hball))⟩
  · intro x hx
    obtain ⟨q,hq,hx⟩ := Set.mem_iUnion₂.mp hx
    exact M.gaugeOrbit_subset_massiveZeros q (hS hq) hx
end
end BFSSQuantum.AlgebraData
namespace BFSSQuantum.AlgebraData
noncomputable section
open Matrix Finset Set
open scoped Matrix.Norms.L2Operator
variable {N : ℕ} (M : AlgebraData N)

lemma colorConjugate_inner (U : ColorMatrix N) (hU : U ∈ unitary (ColorMatrix N))
    (a b : ColorVector N) :
    inner ℝ (M.colorConjugate U a) (M.colorConjugate U b) = inner ℝ a b := by
  apply Complex.ofReal_injective
  rw [M.colorEmbed_inner,M.colorEmbed_inner,M.colorEmbed_conjugate U hU,M.colorEmbed_conjugate U hU]
  have hu : Uᴴ*U = 1 := (Unitary.mem_iff.mp hU).1
  have hp : (U*M.colorEmbed a*Uᴴ)*(U*M.colorEmbed b*Uᴴ) =
      U*(M.colorEmbed a*M.colorEmbed b)*Uᴴ := by
    calc
      _ = U*M.colorEmbed a*(Uᴴ*U)*M.colorEmbed b*Uᴴ := by simp only [mul_assoc]
      _ = _ := by rw [hu]; simp only [mul_one,mul_assoc]
  rw [hp,Matrix.trace_mul_cycle,hu,one_mul]

lemma gaugeConjugate_inner (U : ColorMatrix N) (hU : U ∈ unitary (ColorMatrix N))
    (x y : Boson N) : inner ℝ (M.gaugeConjugate U x) (M.gaugeConjugate U y) = inner ℝ x y := by
  rw [spatialColor_inner,spatialColor_inner]
  apply Finset.sum_congr rfl
  intro i hi
  exact M.colorConjugate_inner U hU (spatialColor x i) (spatialColor y i)

def gaugeAction (U : unitary (ColorMatrix N)) (x : Boson N) : Boson N := M.gaugeConjugate U x

lemma gaugeAction_one (x : Boson N) : M.gaugeAction 1 x = x := M.gaugeConjugate_one x

lemma gaugeAction_mul (U V : unitary (ColorMatrix N)) (x : Boson N) :
    M.gaugeAction (U*V) x = M.gaugeAction U (M.gaugeAction V x) := M.gaugeConjugate_mul U V V.prop x

lemma gaugeAction_inv (U : unitary (ColorMatrix N)) (x : Boson N) :
    M.gaugeAction U⁻¹ (M.gaugeAction U x) = x := by
  rw [←M.gaugeAction_mul,inv_mul_cancel,M.gaugeAction_one]

def gaugeStabilizer (q : Boson N) : Subgroup (unitary (ColorMatrix N)) where
  carrier := {U | M.gaugeAction U q = q}
  one_mem' := M.gaugeAction_one q
  mul_mem' hU hV := by
    change M.gaugeAction _ q = q at hU hV ⊢
    rw [M.gaugeAction_mul,hV,hU]
  inv_mem' {U} hU := by
    have he := M.gaugeAction_inv U q
    rw [hU] at he
    exact he

lemma mem_gaugeStabilizer (q : Boson N) (U : unitary (ColorMatrix N)) :
    U ∈ M.gaugeStabilizer q ↔ M.gaugeAction U q = q := Iff.rfl

lemma gaugeStabilizer_isClosed (q : Boson N) :
    IsClosed (M.gaugeStabilizer q : Set (unitary (ColorMatrix N))) :=
  isClosed_eq ((M.gaugeConjugate_continuous q).comp continuous_subtype_val) continuous_const

lemma gaugeStabilizer_isCompact (hN : 2 ≤ N) (q : Boson N) :
    IsCompact (M.gaugeStabilizer q : Set (unitary (ColorMatrix N))) := by
  have hc : IsCompact (Set.univ : Set (unitary (ColorMatrix N))) :=
    isCompact_iff_isCompact_univ.mp (BFSSOrbit.unitary_compact hN)
  exact hc.of_isClosed_subset (M.gaugeStabilizer_isClosed q) (Set.subset_univ _)

lemma gaugeOrbit_fiber (q : Boson N) (U V : unitary (ColorMatrix N)) :
    M.gaugeAction U q = M.gaugeAction V q ↔ V⁻¹*U ∈ M.gaugeStabilizer q := by
  rw [M.mem_gaugeStabilizer,M.gaugeAction_mul]
  constructor
  · intro he
    rw [he,M.gaugeAction_inv]
  · intro he
    have hh := congrArg (M.gaugeAction V) he
    rw [←M.gaugeAction_mul,mul_inv_cancel,M.gaugeAction_one] at hh
    exact hh

lemma gaugeConjugate_linear (U : ColorMatrix N) :
    ∃ L : Boson N →ₗ[ℝ] Boson N, ∀ x, L x = M.gaugeConjugate U x := by
  refine ⟨{toFun := M.gaugeConjugate U, map_add' := ?_, map_smul' := ?_},fun _ => rfl⟩
  · intro x y
    ext p
    change M.colorConjugate U (spatialColor (x+y) p.1) p.2 = _
    rw [show spatialColor (x+y) p.1 = spatialColor x p.1+spatialColor y p.1 from rfl,map_add]
    rfl
  · intro c x
    ext p
    change M.colorConjugate U (spatialColor (c • x) p.1) p.2 = _
    rw [show spatialColor (c • x) p.1 = c • spatialColor x p.1 from rfl,map_smul]
    rfl

lemma gaugeTangent_equivariant (U : ColorMatrix N) (hU : U ∈ unitary (ColorMatrix N))
    (q : Boson N) (w : ColorVector N) :
    M.gaugeTangent (M.gaugeConjugate U q) (M.colorConjugate U w) =
      M.gaugeConjugate U (M.gaugeTangent q w) := by
  ext p
  change M.colorLie (M.colorConjugate U w)
      (spatialColor (M.gaugeConjugate U q) p.1) p.2 =
    M.colorConjugate U (spatialColor (M.gaugeTangent q w) p.1) p.2
  rw [M.spatialColor_gaugeConjugate,M.spatialColor_gaugeTangent,M.colorConjugate_lie U hU]

lemma colorConjugate_inverse (U : ColorMatrix N) (hU : U ∈ unitary (ColorMatrix N))
    (a : ColorVector N) : M.colorConjugate U (M.colorConjugate Uᴴ a) = a := by
  have hu : U*Uᴴ = 1 := (Unitary.mem_iff.mp hU).2
  rw [← M.colorConjugate_mul U Uᴴ (Unitary.star_mem hU),hu,M.colorConjugate_one]

lemma normalSlice_equivariant (U : ColorMatrix N) (hU : U ∈ unitary (ColorMatrix N))
    (q z : Boson N) (hz : z ∈ M.normalSlice q) :
    M.gaugeConjugate U z ∈ M.normalSlice (M.gaugeConjugate U q) := by
  rw [normalSlice,Submodule.mem_orthogonal'] at hz ⊢
  intro v hv
  obtain ⟨w,rfl⟩ := hv
  have hw := M.colorConjugate_inverse U hU w
  rw [←hw,M.gaugeTangent_equivariant U hU,M.gaugeConjugate_inner U hU]
  exact hz (M.gaugeTangent q (M.colorConjugate Uᴴ w)) ⟨M.colorConjugate Uᴴ w,rfl⟩

lemma stabilizer_preserves_normalSlice (q z : Boson N) (hz : z ∈ M.normalSlice q)
    (U : unitary (ColorMatrix N)) (hU : U ∈ M.gaugeStabilizer q) :
    M.gaugeAction U z ∈ M.normalSlice q := by
  have he := M.normalSlice_equivariant U U.prop q z hz
  change M.gaugeAction U z ∈ M.normalSlice (M.gaugeAction U q) at he
  rw [M.mem_gaugeStabilizer q U |>.mp hU] at he
  exact he
end
end BFSSQuantum.AlgebraData

end OAI
