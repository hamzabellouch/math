import OAI.Analysis.AncientFlat.Evolution.LowerTopInterior
import OAI.Analysis.AncientFlat.Regularity.LowerOrderHolder
import OAI.Analysis.AncientFlat.Geometry.InteriorSchauder

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff Laplacian
namespace ParabolicLowerOrder
open ParabolicInterior ParabolicLocalization ParabolicInterpolation ClassicalIBP
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

theorem lower_interior_schauder (α κ K : ℝ) (hα : 0<α) (hα1 : α<1) (hκ : 0<κ) (hK : 0≤K) :
    ∃ C : ℝ, 0<C ∧ ∀ (a : V × ℝ → ℝ) (b : V × ℝ → ℂ) (c : Coefficients V),
      HolderBound α (cylinder 2) a K → HolderBound α (cylinder 2) b K → (∀ j, HolderBound α (cylinder 2) (c j) K) →
      (∀ p ∈ cylinder 2, κ≤a p) →
      ∀ (u ut f : ℝ → V → ℂ) (F U : ℝ), 0≤F → 0≤U →
      (∀ t : ℝ, ContDiff ℝ 4 (u t)) →
      (∀ p ∈ cylinder 2, HasDerivAt (fun t => u t p.1) (ut p.2 p.1) p.2) →
      (∃ M : ℝ, 0≤M ∧ JetBound α (cylinder 2) u ut M) →
      HolderBound α (cylinder 2) (fun p => f p.2 p.1) F →
      (∀ p ∈ cylinder 2, ‖u p.2 p.1‖≤U) →
      (∀ p ∈ cylinder 2, ut p.2 p.1+(a p : ℂ)*Δ (Δ (u p.2)) p.1+b p*u p.2 p.1+spatialLower c u p=f p.2 p.1) →
      JetBound α (cylinder 1) u ut (C*(F+U)) := by
  let : MeasurableSpace V := borel V
  let : BorelSpace V := ⟨rfl⟩
  obtain ⟨Ct,hCt,Htop⟩ := lower_interior_fourth_seminorm (V := V) α κ K hα hα1 hκ hK
  obtain ⟨Cs,hCs,Hsup⟩ := fourth_sup_epsilon (V := V) (E := ℂ) α 1 (6/5) (5/4) hα (by norm_num) (by norm_num)
  obtain ⟨Cl,hCl,Hlow⟩ := lower_jet_interpolation (V := V) (E := ℂ) α 1 1 (9/8) hα hα1 (by norm_num) (by norm_num)
  let T : (V [×4]→L[ℝ] ℂ) →L[ℝ] ℂ := traceFour
  let N := Ct+Cs
  let D := 22*(2097152+N)
  let A := 1+(1+K*‖T‖)*N+K+3*K*D
  let L := A+Cl
  let C := N+L+1+2*K*‖T‖*N+8*K*L
  have hN : 0<N := by dsimp [N]; positivity
  have hD : 0<D := by dsimp [D]; positivity
  have hA : 0<A := by dsimp [A]; positivity
  have hL : 0<L := by dsimp [L]; positivity
  have hC : 0<C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro a b c ha hb hc hell u ut f F U hF hU hs hd hj hf hu he
  let S := F+U
  have hS : 0≤S := add_nonneg hF hU
  have hUS : U≤S := by dsimp [S]; linarith
  have hFS : F≤S := by dsimp [S]; linarith
  have HT := Htop a b c ha hb hc hell u ut f F U hF hU hs hd hj hf hu he
  have hmem (t : ℝ) (ht : t∈Ioc (-1) 0) (x : V) (hx : ‖x‖<5/4) : (x,t)∈cylinder (5/4) :=
    ⟨hx,by norm_num; linarith [ht.1],ht.2⟩
  have hsub : (cylinder (5/4) : Set (V × ℝ))⊆cylinder 2 := cylinder_mono (by norm_num) (by norm_num)
  have hs12 : (cylinder 1 : Set (V × ℝ))⊆cylinder 2 := cylinder_mono (by norm_num) (by norm_num)
  have hs1top : (cylinder 1 : Set (V × ℝ))⊆cylinder (5/4) := cylinder_mono (by norm_num) (by norm_num)
  have HN (t : ℝ) (ht : t∈Ioc (-1) 0) (x : V) (hx : ‖x‖<6/5) :
      ‖iteratedFDeriv ℝ 4 (u t) x‖≤N*S := by
    have hh := Hsup (u t) (hs t) U (Ct*S) hU (by positivity)
      (fun y hy => hu (y,t) (hsub (hmem t ht y hy)))
      (fun y hy z hz => by
        simpa only [pdist,Prod.fst,Prod.snd,sub_self,abs_zero,Real.zero_rpow (by norm_num : (1:ℝ)/4≠0),add_zero] using
          HT (y,t) (hmem t ht y hy) (z,t) (hmem t ht z hz)) x hx
    apply hh.trans
    dsimp [N]
    nlinarith [mul_le_mul_of_nonneg_left hUS hCs.le]
  have HD (t : ℝ) (ht : t∈Ioc (-1) 0) (x : V) (hx : ‖x‖<9/8) (j : ℕ) (hj : j≤3) :
      ‖iteratedFDeriv ℝ j (u t) x‖≤D*S := by
    have H := lower_jet_bound j hj (u t) (hs t) x (6/5) (1/128) U (N*S) (by norm_num) hU (by positivity)
      (by linarith) (fun y hy => hu (y,t) (hsub (hmem t ht y (by linarith)))) (HN t ht)
    have hp : (1/128:ℝ)^3≤(1/128:ℝ)^j := pow_le_pow_of_le_one (by norm_num) (by norm_num) hj
    have hdiv : U/(1/128:ℝ)^j≤2097152*U := by
      have hd := div_le_div_of_nonneg_left hU (by norm_num : (0:ℝ)<(1/128)^3) hp
      norm_num at hd
      exact hd.trans_eq (by ring)
    have hpow : (1/128:ℝ)^(4-j)≤1 := pow_le_one₀ (by norm_num) (by norm_num)
    dsimp [D]
    nlinarith [mul_le_mul_of_nonneg_right hpow (mul_nonneg hN.le hS)]
  have Htime (t : ℝ) (ht : t∈Ioc (-1) 0) (x : V) (hx : ‖x‖<9/8) : ‖ut t x‖≤A*S := by
    have hp := hsub (hmem t ht x (by linarith))
    have heq : ut t x=f t x-(a (x,t) : ℂ)*Δ (Δ (u t)) x-b (x,t)*u t x-spatialLower c u (x,t) := by
      have he := he (x,t) hp; dsimp only at he; linear_combination he
    have hbi : ‖Δ (Δ (u t)) x‖≤‖T‖*(N*S) := by
      rw [bilaplacian_eq_traceFour _ (hs t)]
      exact (T.le_opNorm _).trans (mul_le_mul_of_nonneg_left (HN t ht x (by linarith)) (norm_nonneg T))
    have hlow : ‖spatialLower c u (x,t)‖≤3*K*(D*S) := by
      apply (norm_sum_le _ _).trans
      calc
        _ ≤ ∑ j : Fin 3, K*(D*S) := Finset.sum_le_sum (fun j _ =>
          ((c j (x,t)).le_opNorm _).trans (mul_le_mul ((hc j).1 (x,t) hp) (HD t ht x hx (j.val+1) (by omega)) (norm_nonneg _) hK))
        _ = _ := by simp; ring
    rw [heq]
    apply (norm_sub_le _ _).trans
    apply (add_le_add (norm_sub_le _ _) le_rfl).trans
    apply (add_le_add (add_le_add (norm_sub_le _ _) le_rfl) le_rfl).trans
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs]
    have h1 := mul_le_mul (ha.1 (x,t) hp) hbi (norm_nonneg _) hK
    have h2 := mul_le_mul (hb.1 (x,t) hp) (hu (x,t) hp) (norm_nonneg _) hK
    have hF' := (hf.1 (x,t) hp).trans hFS
    have hU' := mul_le_mul_of_nonneg_left hUS hK
    have hNS : 0≤N*S := by positivity
    simp only [Real.norm_eq_abs] at h1
    dsimp [A]; nlinarith
  have hNA : N≤A := by dsimp [A]; nlinarith [mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤3) hK) hD.le,mul_nonneg hK (norm_nonneg T), mul_nonneg (mul_nonneg hK (norm_nonneg T)) hN.le]
  have HL (j : ℕ) (hj : j≤3) : HolderBound α (cylinder 1)
      (fun p => iteratedFDeriv ℝ j (u p.2) p.1) (L*S) := by
    have hh := Hlow u ut (Ioc (-1) 0) ordConnected_Ioc U (A*S) hU (by positivity)
      (fun t _ => hs t) (fun t ht x hx => hd (x,t) (hsub (hmem t ht x (by linarith))))
      Htime (fun t ht x hx => hu (x,t) (hsub (hmem t ht x (by linarith))))
      (fun t ht x hx => (HN t ht x (by linarith)).trans (mul_le_mul_of_nonneg_right hNA hS)) j hj
    have hdom : {p : V × ℝ | ‖p.1‖<1 ∧ p.2∈Ioc (-1) 0}=cylinder 1 := by ext p; simp [cylinder]
    rw [hdom] at hh
    exact hh.mono (by dsimp [L]; nlinarith [mul_le_mul_of_nonneg_left hUS hCl.le])
  have H4 : HolderBound α (cylinder 1) (fun p => iteratedFDeriv ℝ 4 (u p.2) p.1) (N*S) := by
    refine ⟨fun p hp => HN p.2 (by simpa [cylinder] using hp.2) p.1 (by linarith [hp.1]),?_⟩
    intro p hp z hz
    have ht := HT p (hs1top hp) z (hs1top hz)
    apply ht.trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by dsimp [N]; linarith : Ct≤N) hS)
      (Real.rpow_nonneg (pdist_nonneg p z) _)
  have hCT : 0≤2*K*‖T‖*N+8*K*L := by positivity
  have hNC : N≤C := by dsimp [C]; linarith
  have hLC : L≤C := by dsimp [C]; linarith
  constructor
  · intro j hj
    rcases lt_or_eq_of_le hj with hj | rfl
    · exact (HL j (by omega)).mono (mul_le_mul_of_nonneg_right hLC hS)
    · exact H4.mono (mul_le_mul_of_nonneg_right hNC hS)
  · have HB : HolderBound α (cylinder 1) (fun p => Δ (Δ (u p.2)) p.1) (‖T‖*(N*S)) := by
      convert H4.clm T using 1
      ext p; exact bilaplacian_eq_traceFour _ (hs p.2) p.1
    have Hab := (ha.restrict hs12).smul HB hK (by positivity)
    have HL0 : HolderBound α (cylinder 1) (fun p => u p.2 p.1) (L*S) :=
      HolderBound.of_jet_zero u (HL 0 (by omega))
    have Hbu := (hb.restrict hs12).mul HL0 hK (by positivity)
    have Hlower := lower_holder hK (show 0≤L*S by positivity) c u
      (fun j => (hc j).restrict hs12) (fun j => HL (j.val+1) (by omega))
    have Hresult := (((hf.restrict hs12).add Hab.neg).add Hbu.neg).add Hlower.neg
    have hbound : F+2*K*(‖T‖*(N*S))+2*K*(L*S)+6*K*(L*S)≤C*S := by
      have hNLS : 0≤(N+L)*S := by positivity
      dsimp [C]; nlinarith
    have Hresult := Hresult.mono hbound
    have heq (p : V × ℝ) (hp : p∈cylinder 1) :
        ut p.2 p.1=((f p.2 p.1+-(a p • Δ (Δ (u p.2)) p.1))+-(b p*u p.2 p.1))+-spatialLower c u p := by
      rw [Complex.real_smul]; have h := he p (hs12 hp); linear_combination h
    constructor
    · intro p hp
      simpa only [heq p hp] using Hresult.1 p hp
    · intro p hp z hz
      dsimp only
      rw [heq p hp,heq z hz]
      exact Hresult.2 p hp z hz
end ParabolicLowerOrder

end

end OAI
