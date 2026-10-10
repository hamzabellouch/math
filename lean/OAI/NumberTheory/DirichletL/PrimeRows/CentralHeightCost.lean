import OAI.NumberTheory.DirichletL.PrimeRows.CentralTargetCost
import OAI.NumberTheory.DirichletL.PrimeRows.CubeScale

namespace OAI

noncomputable section
open scoped Classical Topology
open Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O

theorem cube_height_power_eventually (n : ℕ) (τ p loss : ℝ)
    (hτ : 0<τ) (hp : 0≤p) (hgap : τ*p<loss) :
    ∀ᶠ Z : ℝ in atTop,∀i : ℕ,i≤n → (3+(3*i+2:ℕ)*Z^τ)^p≤Z^loss := by
  have hh := HeckeDyadic.constant_absorbed_eventually ((3*(n:ℝ)+5)^p)
    (loss-τ*p) (by linarith)
  filter_upwards [hh,eventually_ge_atTop (1:ℝ)] with Z hC hZ
  intro i hi
  have hZp : 0<Z := zero_lt_one.trans_le hZ
  have hpow : 1≤Z^τ := Real.one_le_rpow hZ hτ.le
  have hi' : (i:ℝ)≤n := by exact_mod_cast hi
  have hx : 3+(3*i+2:ℕ)*Z^τ≤(3*(n:ℝ)+5)*Z^τ := by push_cast;nlinarith
  calc
    _ ≤ ((3*(n:ℝ)+5)*Z^τ)^p := Real.rpow_le_rpow (by positivity) hx hp
    _ = (3*(n:ℝ)+5)^p*Z^(τ*p) := by
      rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hZp.le _),←Real.rpow_mul hZp.le]
    _ ≤ Z^(loss-τ*p)*Z^(τ*p) := mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hZp.le _)
    _ = Z^loss := by rw [←Real.rpow_add hZp];congr 1;ring

theorem central_remaining_rowCost_scale (e eps τ loss : ℝ) (n : ℕ)
    (he : 0<e) (he' : e<1/1000) (heps : 0<eps) (hτ : 0<τ)
    (hgap : τ*(2+4*eps)<loss)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S) :
    ∃C : ℝ,0<C ∧ ∀ᶠ Z : ℝ in atTop,∀(η : Character) (u : FreeRow)
      {ι : Type*} [Fintype ι] (ψ : ι→Character) (a : ℝ) (i : ℕ),i≤n →
      51/100≤a → a≤1 →
      detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*Z^τ)<a+2*e →
      ∀x w z : ℂ,x.re=a+16*e → w.re=1-a-6*e → z.re=17/50 → |x.im|≤(3*i+2:ℕ)*Z^τ →
      ‖centralRemainingScalar S hS η u x w z‖*
        ProbeCentralRepeatedProduct.rowCost S hS.prime u a e eps ((3*i+2:ℕ)*Z^τ)≤
        C*(η.modulus.absNorm:ℝ)^(2*eps)*rowNorm u^(a-1/2+12*e+7*eps)*Z^loss := by
  obtain ⟨C,hC,hbound⟩ := central_remaining_rowCost_bound e eps he he' heps S hS hfirst
  refine ⟨C,hC,?_⟩
  filter_upwards [cube_height_power_eventually n τ (2+4*eps) loss hτ (by positivity) hgap,
    (tendsto_rpow_atTop hτ).eventually (eventually_gt_atTop (2:ℝ))] with Z hheight hZ
  intro η u ι _ ψ a i hi ha ha1 hbin x w z hx hw hz hxi
  have hb := hbound η u ψ (Z^τ) a ((3*i+2:ℕ)*Z^τ) i hZ ha ha1 le_rfl hbin x w z hx hw hz hxi
  exact hb.trans (mul_le_mul_of_nonneg_left (hheight i hi) (by unfold rowNorm;positivity))

end SevenEighths.ProbeHighRowFamily

end

end OAI
