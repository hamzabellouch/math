import Mathlib
import OAI.GroupTheory.SimpleAmenable.RandomFields.AveragingUniformCovariance

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section PolygonCovarianceEnergy
open Classical

noncomputable def flagMatrixDifference {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (g : polygonFullGroup a m) (χ : (ℝ×ℝ) → ℝ) (ρ N r η κ : ℝ)
    (p : FlagSite a m D v × FlagSite a m D v) : ℝ :=
  flagAveragingMatrix χ ρ N r η κ p.1 p.2-
    flagAveragingMatrix χ ρ N r η κ (flagSiteAction hD g p.1) (flagSiteAction hD g p.2)

theorem flagMatrixDifference_correlation {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (g : polygonFullGroup a m) (χ : (ℝ×ℝ) → ℝ)
    (hχ : ∀x,χ x∈Set.Icc (0:ℝ) 1) {K L ρ η κ : ℝ}
    (hK : 0<K) (hcompact : ∀x,K ≤ ‖x‖ → χ x=0)
    (hL : 0≤L) (hρ : 0<ρ) (hη : 0<η) (hκ : 0<κ)
    (hLip : ∀x y,|χ x-χ y| ≤ L*(|x.1-y.1|+|x.2-y.2|)) :
    ∃R C : ℝ,0≤R ∧ 0≤C ∧ ∀N r r' : ℝ,1≤N → 1≤r → 1≤r' →
      R ≤ κ/(r/N) → R ≤ κ/(r'/N) →
      ∀T : Finset (FlagSite a m D v × FlagSite a m D v),
      |∑p∈T,flagMatrixDifference hD g χ ρ N r η κ p*
        flagMatrixDifference hD g χ ρ N r' η κ p| ≤ C*(r/r') := by
  obtain ⟨R,A,hR,hA,he⟩ := flagAveragingMatrix_uniform_difference (v:=v) hD g
  let B := A*(2*L+1/κ)/(ρ*η^2)
  let H := 2*(m:ℝ)*(2*(D:ℝ)^2*K+2)^2*(4*(D:ℝ)^2*η+2)^2
  have hB : 0≤B := by dsimp [B]; positivity
  have hH : 0≤H := by dsimp [H]; positivity
  refine ⟨R,H*B^2,hR,mul_nonneg hH (sq_nonneg _),?_⟩
  intro N r r' hN hr hr' hfine hfine' T
  have hN₀ : 0<N := lt_of_lt_of_le zero_lt_one hN
  have hr₀ : 0<r := lt_of_lt_of_le zero_lt_one hr
  have hr'₀ : 0<r' := lt_of_lt_of_le zero_lt_one hr'
  have hb (r : ℝ) (hr : 1≤r) (hh : R ≤ κ/(r/N)) (p : FlagSite a m D v × FlagSite a m D v) :
      |flagMatrixDifference hD g χ ρ N r η κ p| ≤ B/(N*r) :=
    he χ hχ L ρ N r η κ hL hρ hN₀ hr hη hκ hh hLip p.1 p.2
  have hs (S : Finset (FlagSite a m D v × FlagSite a m D v))
      (hh : ∀p∈S,flagMatrixDifference hD g χ ρ N r η κ p≠0) : (S.card:ℝ) ≤ H*N^2*r^2 :=
    flagAveragingMatrix_difference_support hD g χ hK hcompact ρ κ hN hr hη S hh
  calc
    _ ≤ (H*N^2*r^2)*(B/(N*r))*(B/(N*r')) :=
      finite_correlation_bound T _ _ (by positivity) (by positivity)
        (fun p _ => hb r hr hfine p) (fun p _ => hb r' hr' hfine' p) (fun S _ hh => hs S hh)
    _ = _ := by field_simp

theorem flagMatrixDifference_dyadic_energy {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (g : polygonFullGroup a m) (χ : (ℝ×ℝ) → ℝ)
    (hχ : ∀x,χ x∈Set.Icc (0:ℝ) 1) {K L ρ η κ : ℝ}
    (hK : 0<K) (hcompact : ∀x,K ≤ ‖x‖ → χ x=0)
    (hL : 0≤L) (hρ : 0<ρ) (hη : 0<η) (hκ : 0<κ)
    (hLip : ∀x y,|χ x-χ y| ≤ L*(|x.1-y.1|+|x.2-y.2|)) :
    ∃R C : ℝ,0≤R ∧ 0≤C ∧ ∀N : ℝ,1≤N → ∀I : Finset ℕ,
      (∀i∈I,R ≤ κ/((2:ℝ)^i/N)) → ∀w : ℝ,
      ∀T : Finset (FlagSite a m D v × FlagSite a m D v),
      ∑p∈T,(w*∑i∈I,flagMatrixDifference hD g χ ρ N ((2:ℝ)^i) η κ p)^2 ≤
        4*C*(I.card:ℝ)*w^2 := by
  obtain ⟨R,C,hR,hC,hcorr⟩ := flagMatrixDifference_correlation (v:=v) hD g χ hχ
    hK hcompact hL hρ hη hκ hLip
  refine ⟨R,C,hR,hC,fun N hN I hfine w T => ?_⟩
  apply finite_dyadic_energy T I _ hC
  intro i hi j hj _
  exact hcorr N ((2:ℝ)^i) ((2:ℝ)^j) hN (one_le_pow₀ (by norm_num))
    (one_le_pow₀ (by norm_num)) (hfine i hi) (hfine j hj) T

end PolygonCovarianceEnergy

section PolygonDyadicRowEnergy
open Classical

theorem finite_sum_row_energy {α ι : Type*} (S : Finset α) (I : Finset ι)
    (f : ι → α → ℝ) (b : ι → ℝ) (hb : ∀i∈I,0 ≤ b i)
    (he : ∀i∈I,∑x∈S,(f i x)^2 ≤ (b i)^2) :
    ∑x∈S,(∑i∈I,f i x)^2 ≤ (∑i∈I,b i)^2 := by
  have hpair (i j : ι) (hi : i∈I) (hj : j∈I) : ∑x∈S,f i x*f j x ≤ b i*b j := by
    apply le_of_sq_le_sq _ (mul_nonneg (hb i hi) (hb j hj))
    calc
      _ ≤ (∑x∈S,(f i x)^2)*(∑x∈S,(f j x)^2) := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
      _ ≤ (b i)^2*(b j)^2 := mul_le_mul (he i hi) (he j hj)
        (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (sq_nonneg _)
      _ = _ := (mul_pow _ _ _).symm
  calc
    _ = ∑i∈I,∑j∈I,∑x∈S,f i x*f j x := by
      simp_rw [pow_two,Finset.sum_mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
    _ ≤ ∑i∈I,∑j∈I,b i*b j :=
      Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun j hj => hpair i j hi hj))
    _ = _ := by rw [pow_two,Finset.sum_mul_sum]

theorem finite_half_geometric_tail (I : Finset ℕ) (n : ℕ) (hn : ∀i∈I,n ≤ i) :
    ∑i∈I,(1/2:ℝ)^i ≤ 2*(1/2:ℝ)^n := by
  have hi : Set.InjOn (fun i => i-n) I := by
    intro i hi j hj he
    have hi₀ := hn i hi
    have hj₀ := hn j hj
    change i-n=j-n at he
    omega
  have he : (∑i∈I,(1/2:ℝ)^i)=(1/2:ℝ)^n*(∑j∈I.image (fun i => i-n),(1/2:ℝ)^j) := by
    rw [Finset.sum_image hi,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← pow_add,Nat.add_sub_of_le (hn i hi)]
  rw [he]
  have hh := mul_le_mul_of_nonneg_left (finite_half_geometric_sum (I.image (fun i => i-n)))
    (pow_nonneg (by norm_num : (0:ℝ) ≤ 1/2) n)
  simpa [mul_comm] using hh

noncomputable def flagRowConstant (D : ℕ) (ρ η : ℝ) : ℝ :=
  (4*(D:ℝ)^2*η+2)/(ρ*η^2)

theorem flagAveragingMatrix_row_energy_uniform {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (χ : (ℝ×ℝ) → ℝ) (hχ : ∀x,χ x∈Set.Icc (0:ℝ) 1)
    {ρ N r η κ : ℝ} (hρ : 0<ρ) (hN : 0<N) (hr : 1≤r)
    (hη : 0<η) (hκ : 0<κ) (z : FlagSite a m D v) (S : Finset (FlagSite a m D v)) :
    ∑y∈S,(flagAveragingMatrix χ ρ N r η κ z y)^2 ≤ (flagRowConstant D ρ η/r)^2 := by
  have hr₀ : 0<r := lt_of_lt_of_le zero_lt_one hr
  have hd : 0<ρ*(r*η)^2 := by positivity
  have hn : 4*(D:ℝ)^2*r*η+2 ≤ (4*(D:ℝ)^2*η+2)*r := by nlinarith
  calc
    _ ≤ (4*(D:ℝ)^2*r*η+2)^2/(ρ*(r*η)^2)^2 :=
      flagAveragingMatrix_row_energy hD χ hχ hρ hN hr₀ hη hκ z S
    _ ≤ ((4*(D:ℝ)^2*η+2)*r)^2/(ρ*(r*η)^2)^2 := by
      gcongr
    _ = _ := by unfold flagRowConstant; field_simp

theorem flagAveragingMatrix_dyadic_row_energy {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (χ : (ℝ×ℝ) → ℝ) (hχ : ∀x,χ x∈Set.Icc (0:ℝ) 1)
    {ρ N η κ : ℝ} (hρ : 0<ρ) (hN : 0<N) (hη : 0<η) (hκ : 0<κ)
    (I : Finset ℕ) (n : ℕ) (hn : ∀i∈I,n ≤ i) (w : ℝ)
    (z : FlagSite a m D v) (S : Finset (FlagSite a m D v)) :
    ∑y∈S,(w*∑i∈I,flagAveragingMatrix χ ρ N ((2:ℝ)^i) η κ z y)^2 ≤
      (2*flagRowConstant D ρ η*w/(2:ℝ)^n)^2 := by
  have hC : 0 ≤ flagRowConstant D ρ η := by unfold flagRowConstant; positivity
  have hei := finite_sum_row_energy S I
    (fun i y => flagAveragingMatrix χ ρ N ((2:ℝ)^i) η κ z y)
    (fun i => flagRowConstant D ρ η/(2:ℝ)^i)
    (by intro i hi; positivity)
    (fun i _ => flagAveragingMatrix_row_energy_uniform hD χ hχ hρ hN
      (one_le_pow₀ (by norm_num)) hη hκ z S)
  have hsum : ∑i∈I,flagRowConstant D ρ η/(2:ℝ)^i ≤ 2*flagRowConstant D ρ η/(2:ℝ)^n := by
    have h : (∑i∈I,flagRowConstant D ρ η/(2:ℝ)^i)=flagRowConstant D ρ η*(∑i∈I,(1/2:ℝ)^i) := by
      simp [Finset.mul_sum,div_eq_mul_inv]
    rw [h]
    have hh := mul_le_mul_of_nonneg_left (finite_half_geometric_tail I n hn) hC
    simpa [div_pow,div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using hh
  have hsum₀ : 0 ≤ ∑i∈I,flagRowConstant D ρ η/(2:ℝ)^i :=
    Finset.sum_nonneg (fun _ _ => by positivity)
  calc
    _ = w^2*(∑y∈S,(∑i∈I,flagAveragingMatrix χ ρ N ((2:ℝ)^i) η κ z y)^2) := by
      simp_rw [mul_pow,Finset.mul_sum]
    _ ≤ w^2*(∑i∈I,flagRowConstant D ρ η/(2:ℝ)^i)^2 :=
      mul_le_mul_of_nonneg_left hei (sq_nonneg _)
    _ ≤ w^2*(2*flagRowConstant D ρ η/(2:ℝ)^n)^2 := by gcongr
    _ = _ := by ring

end PolygonDyadicRowEnergy

end SimpleAmenable
end
end

end OAI
