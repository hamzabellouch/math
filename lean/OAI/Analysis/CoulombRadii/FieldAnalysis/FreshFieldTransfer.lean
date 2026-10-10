import Mathlib
import OAI.Analysis.CoulombRadii.RandomFields.EnsembleTransfer

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
noncomputable section
namespace Coulomb

lemma fresh_raw_coulomb_weight_integrable {m k : ℕ} (u : H1Vector (m+k)) (y : Space) (s : Spins m) :
    Integrable (fun x => mass (u.coreSlice s x)*(coreCoulombPotential (u.coreSlice s x).normalized y+
      nuclearPotential (unitNucleus y) x)) := by
  have hc : Integrable (fun x => mass (u.coreSlice s x)*coreCoulombPotential (u.coreSlice s x).normalized y) := by
    simp only [←nuclearEnergy_unit_eq_coreCoulomb]
    change Integrable (fun x => mass (u.coreSlice s x)*potentialForm (nuclearPotential (unitNucleus y))
      (u.coreSlice s x).normalized)
    simp_rw [potentialForm_normalized_weight]
    exact potentialForm_coreSlice_integrable u s _ (fun t => u.core_nuclear_integrable (unitNucleus y) (Fin.append s t))
  have ho := slice_weight_integrable_const u (nuclearPotential (unitNucleus y))
    (u.outer_nuclear_integrable (unitNucleus y)) s
  apply (hc.add ho).congr
  exact Eventually.of_forall (fun x => by dsimp only [Pi.add_apply]; rw [mul_add])

lemma fresh_raw_screened_weight_integrable {J m k : ℕ} (S : Nuclei J)
    (u : H1Vector (m+k)) (y : Space) (s : Spins m) :
    Integrable (fun x => mass (u.coreSlice s x)*(coreScreenedField S (u.coreSlice s x).normalized y-
      nuclearPotential (unitNucleus y) x)) := by
  apply (((mass_coreSlice_integrable u s).mul_const (attraction S y)).sub
    (fresh_raw_coulomb_weight_integrable u y s)).congr
  exact Eventually.of_forall (fun x => by dsimp only [Pi.sub_apply]; unfold coreScreenedField; ring)

lemma fresh_raw_screened_tower {J m k : ℕ} (S : Nuclei J) (u : H1Vector (m+k)) (y : Space) :
    sliceExpectation u (fun s x => coreScreenedField S (u.coreSlice s x).normalized y-
      nuclearPotential (unitNucleus y) x)=attraction S y*mass u-coreCoulombPotential u y := by
  have he : (fun s x => coreScreenedField S (u.coreSlice s x).normalized y-nuclearPotential (unitNucleus y) x)=
      fun s x => attraction S y-(coreCoulombPotential (u.coreSlice s x).normalized y+nuclearPotential (unitNucleus y) x) := by
    funext s x
    unfold coreScreenedField
    ring
  rw [he,sliceExpectation_sub u _ _ (fun s => (mass_coreSlice_integrable u s).mul_const _)
    (fresh_raw_coulomb_weight_integrable u y),sliceExpectation_number,fresh_core_coulomb_tower]

theorem patchTFScreenedField_weight_integrable {J m k : ℕ} (S : Nuclei J) (u : H1Vector (m+k))
    {a b t r ε : ℝ} (ha : 0<a) (hb : 0<b) (hsmall : 18*b≤a)
    (ht : t∈Set.Icc (5*a) (6*a)) (y : Space)
    (hn : ∀ j,20*a≤‖S.position j-y‖) (hr : 0<r) (hra : r≤a) (hε : 0<ε)
    (hcs : ∀ s, ∀ᵐ x, SpatiallySupported (u.coreSlice s x).normalized {z | t≤‖z-y‖}) (s : Spins m) :
    Integrable (fun x => mass (u.coreSlice s x)*patchTFScreenedField S (u.coreSlice s x).normalized ha hb ht.2 y hn y) := by
  have hE := (patchFieldTransferError_integrable_mean S u ha hb hsmall ht y hn hr hra hε hcs).1 s
  apply ((fresh_raw_screened_weight_integrable S u y s).sub hE).congr
  exact Eventually.of_forall (fun x => by dsimp only [Pi.sub_apply]; unfold patchFieldTransferError; ring)

theorem fresh_patch_field_tower {J n : ℕ} (S : Nuclei J) (T : RecordedEnsemble n) (u : H1Vector n)
    (hT : T.Conserves u) (hm : (∑ p,mass (T.vector p))=1)
    {a b t r ε : ℝ} (ha : 0<a) (hb : 0<b) (hsmall : 18*b≤a)
    (ht : t∈Set.Icc (5*a) (6*a)) (y : Space)
    (hn : ∀ j,20*a≤‖S.position j-y‖) (hr : 0<r) (hra : r≤a) (hε : 0<ε)
    (hcs : T.CoreSupported {z | t≤‖z-y‖}) :
    (∑ p,sliceExpectation (T.vector p) (patchFieldTransferError S (T.vector p) ha hb ht.2 y hn))=
      coreScreenedField S u y-(∑ p,sliceExpectation (T.vector p) (fun s x =>
        patchTFScreenedField S ((T.vector p).coreSlice s x).normalized ha hb ht.2 y hn y)) := by
  have hs (p : T.index) (s) : ∀ᵐ x, SpatiallySupported ((T.vector p).coreSlice s x).normalized {z | t≤‖z-y‖} :=
    ((hcs p).coreSlice s).mono (fun x hx => hx.normalized)
  have he (p : T.index) :
      sliceExpectation (T.vector p) (patchFieldTransferError S (T.vector p) ha hb ht.2 y hn)=
      attraction S y*mass (T.vector p)-coreCoulombPotential (T.vector p) y-
      sliceExpectation (T.vector p) (fun s x => patchTFScreenedField S ((T.vector p).coreSlice s x).normalized ha hb ht.2 y hn y) := by
    unfold patchFieldTransferError
    rw [sliceExpectation_sub (T.vector p) _ _ (fresh_raw_screened_weight_integrable S (T.vector p) y)
      (patchTFScreenedField_weight_integrable S (T.vector p) ha hb hsmall ht y hn hr hra hε (hs p)),
      fresh_raw_screened_tower]
  simp only [he,Finset.sum_sub_distrib,←Finset.mul_sum,hm,mul_one,hT.coulomb_potential y,coreScreenedField]

theorem fresh_patch_field_transfer {J n : ℕ} (S : Nuclei J) (T : RecordedEnsemble n) (u : H1Vector n)
    (hT : T.Conserves u) (hm : (∑ p,mass (T.vector p))=1)
    {a b t r ε : ℝ} (ha : 0<a) (hb : 0<b) (hsmall : 18*b≤a)
    (ht : t∈Set.Icc (5*a) (6*a)) (y : Space)
    (hn : ∀ j,20*a≤‖S.position j-y‖) (hr : 0<r) (hra : r≤a) (hε : 0<ε)
    (hcs : T.CoreSupported {z | t≤‖z-y‖}) :
    |coreScreenedField S u y-(∑ p,sliceExpectation (T.vector p) (fun s x =>
      patchTFScreenedField S ((T.vector p).coreSlice s x).normalized ha hb ht.2 y hn y))|≤
      ε+(5/(4*r*ε))*(∑ p,sliceExpectation (T.vector p) (patchSliceTFGap S (T.vector p) ha hb ht.2 y hn))+
      potentialForm (nearPotential y (r+2*b)) u+potentialForm (nearPotential y (2*b)) u+
      Real.sqrt (T.deletedSquare y t b)/a+
      ((tfInteriorConstant thomasFermiKineticConstant/
        (thomasFermiKineticConstant*(5/3:ℝ)))^(3/2:ℝ)/a^6)*(2*Real.pi*r^2) := by
  rw [←fresh_patch_field_tower S T u hT hm ha hb hsmall ht y hn hr hra hε hcs]
  exact ensemble_patch_error_bound S T u hT hm ha hb hsmall ht y hn hr hra hε hcs
end Coulomb
end

end
end

end OAI
