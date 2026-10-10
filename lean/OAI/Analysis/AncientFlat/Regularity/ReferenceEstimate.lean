import OAI.Analysis.AncientFlat.Regularity.CoreSchauder
import OAI.Analysis.AncientFlat.Geometry.Annular
import OAI.Analysis.AncientFlat.Profile.AnnularProfile
import OAI.Analysis.AncientFlat.Weighted.WeightedSourceHolder

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff Laplacian
namespace FlatWeighted
open ParabolicInterior ParabolicAnnular
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] in
lemma core_sigma_lower (p : V × ℝ) (hp : p∈ParabolicCore.outer) : (1:ℝ)/2 ≤ sigma p := by
  unfold sigma
  apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
  have ht : (1:ℝ)/2≤Real.sqrt (-p.2) := (Real.le_sqrt (by norm_num) (by linarith [hp.2.2])).mpr (by norm_num; linarith [hp.2.2])
  nlinarith [sq_nonneg ‖p.1‖]
omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] in
lemma annular_sigma_lower (p : V × ℝ) (hp : p∈ParabolicAnnular.outer) : (1:ℝ)/2 ≤ sigma p := by
  unfold sigma
  apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
  nlinarith [hp.1,Real.sqrt_nonneg (-p.2),norm_nonneg p.1]
lemma reference_estimate (G H : ℝ → ℝ) (c κ α δ a : ℝ)
    (hc : 0<c) (hκ : 0<κ) (hα : 0<α) (hα1 : α<1)
    (hδ : 0<δ) (hδ1 : δ<1) (ha : 0<a)
    (hG : ContDiffOn ℝ ∞ G (Ici 0)) (hH : ContDiffOn ℝ ∞ H (Ici 0))
    (hH0 : H 0=c) (hmatch : ∀ u : ℝ, 0<u → H u=G (u^(-(1:ℝ)/2)))
    (hpos : ∀ y : ℝ, 0≤y → κ≤G y) :
    ∃ C : ℝ, 0<C ∧ ∀ (u ut : ℝ → V → ℂ) (f : V × ℝ → ℂ) (F M : ℝ),
      0≤F → 0≤M → (∀ t : ℝ, ContDiff ℝ 4 (u t)) →
      (∀ p : V × ℝ, p.2<0 → HasDerivAt (fun t => u t p.1) (ut p.2 p.1) p.2) →
      LocallyFiniteJets α u ut → YBound α (-2+2*δ) a F f →
      (∀ p : V × ℝ, p.2<0 → ‖u p.2 p.1‖≤M*(-p.2)^((-1+δ)/2)) →
      (∀ p : V × ℝ, p.2<0 → ut p.2 p.1+(profilePrincipal G p : ℂ)*
        Δ (Δ (u p.2)) p.1+(profilePotential G p : ℂ)*u p.2 p.1=f p) →
      JetBound α ParabolicCore.inner u ut (C*(F+M)) ∧
      JetBound α ParabolicAnnular.inner u ut (C*(F+M)) := by
  let : MeasurableSpace V := borel V
  let : BorelSpace V := ⟨rfl⟩
  obtain ⟨Kc,hKc,hAc,hBc,hEc⟩ := ParabolicCore.profile_core_holder (V := V) G κ α hκ hα hα1 hG hpos
  obtain ⟨Ka,hKa,hAa,hBa,hEa⟩ := profile_annular_holder (V := V) G H c κ α hc hκ hα hα1 hG hH hH0 hmatch hpos
  have hκ' : 0<κ^2/16 := by positivity
  obtain ⟨Cc,hCc,Hc⟩ := ParabolicCore.core_schauder (V := V) α (κ^2/16) Kc hα hα1 hκ' hKc.le
  obtain ⟨Ca,hCa,Ha⟩ := annular_schauder (V := V) α (κ^2/16) Ka δ hα hα1 hκ' hKa.le hδ hδ1
  let D := (1/2:ℝ)^((-2+2*δ)-4)+(1/2:ℝ)^((-2+2*δ)-4)*(1/2:ℝ)^(-α)+2*(1/2:ℝ)^((-2+2*δ)-4)/(a*(1/2))^α
  let B := (1/2:ℝ)^((-1+δ)/2)
  have hD : 0<D := by dsimp [D]; positivity
  have hB : 0<B := by dsimp [B]; positivity
  let C := Cc*(D+B)+Ca*(D+1)
  have hC : 0<C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro u ut f F M hF hM hs hd hj hf hu he
  have hfc : HolderBound α ParabolicCore.outer f (D*F) :=
    hf.holder_on hα.le (by linarith) ha hF (by norm_num : (0:ℝ)<1/2)
      (fun p hp => by linarith [hp.2.2]) core_sigma_lower
  have hfa : HolderBound α ParabolicAnnular.outer f (D*F) :=
    hf.holder_on hα.le (by linarith) ha hF (by norm_num : (0:ℝ)<1/2)
      (fun _ hp => hp.2.2.2) annular_sigma_lower
  have huc : ∀ p∈ParabolicCore.outer, ‖u p.2 p.1‖≤B*M := by
    intro p hp
    have ht : p.2<0 := by linarith [hp.2.2]
    have hb : (-p.2)^((-1+δ)/2)≤B := Real.rpow_le_rpow_of_nonpos (by norm_num) (by linarith [hp.2.2]) (by linarith)
    exact (hu p ht).trans ((mul_le_mul_of_nonneg_left hb hM).trans_eq (mul_comm _ _))
  have hjA : ∀ b : ℝ, b<0 → ∃ N : ℝ, 0≤N ∧ JetBound α (ParabolicAnnular.outer ∩ {p | p.2≤b}) u ut N := by
    intro b hb
    obtain ⟨N,hN,hJ⟩ := hj 5 (by norm_num) b hb
    have hsub : ParabolicAnnular.outer ∩ {p : V × ℝ | p.2≤b} ⊆ {p : V × ℝ | ‖p.1‖≤5 ∧ -5≤p.2 ∧ p.2≤b} := by
      intro p hp
      exact ⟨by linarith [hp.1.2.1],by linarith [hp.1.2.2.1],hp.2⟩
    exact ⟨N,hN,fun n hn => (hJ.1 n hn).restrict hsub,hJ.2.restrict hsub⟩
  have hcJ := Hc (profilePrincipal G) (fun p => (profilePotential G p:ℂ)) hAc hBc hEc u ut
    (fun t x => f (x,t)) (D*F) (B*M) (by positivity) (by positivity) hs
    (fun p hp => hd p (by linarith [hp.2.2])) hj hfc huc (fun p hp => he p (by linarith [hp.2.2]))
  have haJ := Ha (profilePrincipal G) (fun p => (profilePotential G p:ℂ)) hAa hBa hEa u ut
    (fun t x => f (x,t)) (D*F) M (by positivity) hM hs
    (fun p hp => hd p hp.2.2.2) hjA hfa (fun p hp => hu p hp.2.2.2) (fun p hp => he p hp.2.2.2)
  have hcBound : Cc*(D*F+B*M)≤C*(F+M) := by dsimp [C]; nlinarith [mul_nonneg (mul_nonneg hCa.le (by positivity : 0≤D+1)) (show 0≤F+M by positivity),mul_nonneg (mul_nonneg hCc.le hD.le) hM,mul_nonneg (mul_nonneg hCc.le hB.le) hF]
  have haBound : Ca*(D*F+M)≤C*(F+M) := by dsimp [C]; nlinarith [mul_nonneg (mul_nonneg hCc.le (show 0≤D+B by positivity)) (show 0≤F+M by positivity),mul_nonneg (mul_nonneg hCa.le hD.le) hM,mul_nonneg hCa.le hF]
  exact ⟨⟨fun n hn => (hcJ.1 n hn).mono hcBound,hcJ.2.mono hcBound⟩,
    ⟨fun n hn => (haJ.1 n hn).mono haBound,haJ.2.mono haBound⟩⟩
end FlatWeighted

end

end OAI
