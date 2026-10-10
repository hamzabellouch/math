import Mathlib
import OAI.Analysis.CoulombRadii.FieldAnalysis.CorePointMeasurable

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
noncomputable section
namespace Coulomb

lemma sliceExpectation_linear_remainder {m k : ℕ} (u : H1Vector (m+k))
    (G N₁ N₂ D : Spins m → Configuration m → ℝ) (c ε C a : ℝ)
    (hG : ∀ s,Integrable (fun x => mass (u.coreSlice s x)*G s x))
    (hN₁ : ∀ s,Integrable (fun x => mass (u.coreSlice s x)*N₁ s x))
    (hN₂ : ∀ s,Integrable (fun x => mass (u.coreSlice s x)*N₂ s x))
    (hD : ∀ s,Integrable (fun x => mass (u.coreSlice s x)*D s x)) :
    sliceExpectation u (fun s x => ε+c*G s x+N₁ s x+N₂ s x+D s x/a+C)=
      ε*mass u+c*sliceExpectation u G+sliceExpectation u N₁+sliceExpectation u N₂+
        sliceExpectation u D/a+C*mass u := by
  have he (s : Spins m) :
      (∫ x,mass (u.coreSlice s x)*(ε+c*G s x+N₁ s x+N₂ s x+D s x/a+C))=
        ε*(∫ x,mass (u.coreSlice s x))+c*(∫ x,mass (u.coreSlice s x)*G s x)+
        (∫ x,mass (u.coreSlice s x)*N₁ s x)+(∫ x,mass (u.coreSlice s x)*N₂ s x)+
        (∫ x,mass (u.coreSlice s x)*D s x)/a+C*(∫ x,mass (u.coreSlice s x)) := by
    have h0 := (mass_coreSlice_integrable u s).const_mul ε
    have h1 := (hG s).const_mul c
    have hd := (hD s).div_const a
    have hC := (mass_coreSlice_integrable u s).const_mul C
    calc
      _=(∫ x,ε*mass (u.coreSlice s x)+c*(mass (u.coreSlice s x)*G s x)+
        mass (u.coreSlice s x)*N₁ s x+mass (u.coreSlice s x)*N₂ s x+
        (mass (u.coreSlice s x)*D s x)/a+C*mass (u.coreSlice s x)) := by
          apply integral_congr_ae
          exact Eventually.of_forall (fun x => by ring)
      _=_ := by
        have hA := integral_add ((((h0.add h1).add (hN₁ s)).add (hN₂ s)).add hd) hC
        have hB := integral_add (((h0.add h1).add (hN₁ s)).add (hN₂ s)) hd
        have hE := integral_add ((h0.add h1).add (hN₁ s)) (hN₂ s)
        have hF := integral_add (h0.add h1) (hN₁ s)
        have hH := integral_add h0 h1
        simp only [Pi.add_apply] at hA hB hE hF hH
        rw [hA,hB,hE,hF,hH,integral_const_mul,integral_const_mul,integral_const_mul,integral_div]
  unfold sliceExpectation
  simp only [he,Finset.sum_add_distrib,←Finset.mul_sum,←Finset.sum_div,integral_mass_coreSlice]

lemma nearPotential_fresh_expectation {n : ℕ} (T : RecordedEnsemble n) (u : H1Vector n)
    (hT : T.Conserves u) {y : Space} {R t : ℝ} (hs : T.CoreSupported {z | t≤‖z-y‖}) (hRt : R≤t) :
    (∑ p,sliceExpectation (T.vector p) (fun _ x => nearPotential y R x))=
      potentialForm (nearPotential y R) u := by
  rw [←hT.nearPotential y R]
  apply Finset.sum_congr rfl
  intro p _
  rw [sliceExpectation_const (T.vector p) _ (nearPotential_outer_integrable (T.vector p) y R)]
  exact (supported_core_nearPotential (T.vector p) y hRt (hs p)).symm

lemma fresh_deleted_mean_le {n : ℕ} (T : RecordedEnsemble n)
    (hm : (∑ p,mass (T.vector p))=1) (y : Space) (t b : ℝ) :
    (∑ p,sliceExpectation (T.vector p) (fun _ x => localCount {z | t-7*b≤‖z-y‖} x))≤
      Real.sqrt (T.deletedSquare y t b) := by
  apply slice_ensemble_mean_le_sqrt T.out T.core T.vector _ _ _ _ hm
  · exact fun p s => (localCount_measurable (isClosed_le continuous_const (by fun_prop)).measurableSet).aestronglyMeasurable
  · exact fun p s => Eventually.of_forall (fun x => localCount_nonneg _ x)
  · exact fun p s => sliceCount_weight_integrable (T.vector p)
      (isClosed_le continuous_const (by fun_prop)).measurableSet s 2

theorem ensemble_patch_error_bound {J n : ℕ} (S : Nuclei J) (T : RecordedEnsemble n) (u : H1Vector n)
    (hT : T.Conserves u) (hm : (∑ p,mass (T.vector p))=1)
    {a b t r ε : ℝ} (ha : 0<a) (hb : 0<b) (hsmall : 18*b≤a)
    (ht : t∈Set.Icc (5*a) (6*a)) (y : Space)
    (hn : ∀ j,20*a≤‖S.position j-y‖) (hr : 0<r) (hra : r≤a) (hε : 0<ε)
    (hcs : T.CoreSupported {z | t≤‖z-y‖}) :
    |∑ p,sliceExpectation (T.vector p) (patchFieldTransferError S (T.vector p) ha hb ht.2 y hn)|≤
      ε+(5/(4*r*ε))*(∑ p,sliceExpectation (T.vector p) (patchSliceTFGap S (T.vector p) ha hb ht.2 y hn))+
      potentialForm (nearPotential y (r+2*b)) u+potentialForm (nearPotential y (2*b)) u+
      Real.sqrt (T.deletedSquare y t b)/a+
      ((tfInteriorConstant thomasFermiKineticConstant/
        (thomasFermiKineticConstant*(5/3:ℝ)))^(3/2:ℝ)/a^6)*(2*Real.pi*r^2) := by
  have hs (p : T.index) (s) : ∀ᵐ x, SpatiallySupported ((T.vector p).coreSlice s x).normalized {z | t≤‖z-y‖} :=
    ((hcs p).coreSlice s).mono (fun x hx => hx.normalized)
  have HB := (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun p (_ : p∈Finset.univ) =>
    (patchFieldTransferError_integrable_mean S (T.vector p) ha hb hsmall ht y hn hr hra hε (hs p)).2))
  have HE (p : T.index) :
      sliceExpectation (T.vector p) (patchTransferRemainder S (T.vector p) ha hb ht.2 y hn r ε)=
        ε*mass (T.vector p)+(5/(4*r*ε))*sliceExpectation (T.vector p) (patchSliceTFGap S (T.vector p) ha hb ht.2 y hn)+
        sliceExpectation (T.vector p) (fun _ x => nearPotential y (r+2*b) x)+
        sliceExpectation (T.vector p) (fun _ x => nearPotential y (2*b) x)+
        sliceExpectation (T.vector p) (fun _ x => localCount {z | t-7*b≤‖z-y‖} x)/a+
        (((tfInteriorConstant thomasFermiKineticConstant/
          (thomasFermiKineticConstant*(5/3:ℝ)))^(3/2:ℝ)/a^6)*(2*Real.pi*r^2))*mass (T.vector p) := by
    apply sliceExpectation_linear_remainder
    · exact fun s => patchSliceTFGap_weight_integrable S (T.vector p) ha hb ht.2 y hn s (hs p s)
    · exact fun s => slice_weight_integrable_const (T.vector p) _ (nearPotential_outer_integrable (T.vector p) y (r+2*b)) s
    · exact fun s => slice_weight_integrable_const (T.vector p) _ (nearPotential_outer_integrable (T.vector p) y (2*b)) s
    · intro s
      simpa only [pow_one] using sliceCount_weight_integrable (T.vector p)
        (isClosed_le continuous_const (by fun_prop)).measurableSet s 1
  simp only [HE,Finset.sum_add_distrib,←Finset.mul_sum,←Finset.sum_div,hm,mul_one] at HB
  rw [nearPotential_fresh_expectation T u hT hcs (by linarith [ht.1] : r+2*b≤t),
    nearPotential_fresh_expectation T u hT hcs (by linarith [ht.1] : 2*b≤t)] at HB
  have hD := div_le_div_of_nonneg_right (fresh_deleted_mean_le T hm y t b) ha.le
  linarith
end Coulomb
end

end
end

end OAI
