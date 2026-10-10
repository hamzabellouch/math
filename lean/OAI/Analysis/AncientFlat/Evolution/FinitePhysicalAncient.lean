import OAI.Analysis.AncientFlat.Regularity.PhysicalFiniteJets
import OAI.Analysis.AncientFlat.Evolution.PhysicalFromWindow
import OAI.Analysis.AncientFlat.Regularity.MovingFourthHolder

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff ZeroAtInfty BoundedContinuousFunction Laplacian Topology
namespace FlatSimilarity
open ParametrixDilation ParametrixEvolution FlatWeighted
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
local instance finitePhysicalAncientC0SeminormedAddCommGroup : SeminormedAddCommGroup C₀(V,ℂ) := inferInstance
local instance finitePhysicalAncientSourceSeminormedAddCommGroup : SeminormedAddCommGroup (ℝ →ᵇ C₀(V,ℂ)) := inferInstance
def physicalTime (γ : ℝ) (Af Bf : V → ℝ) (f v : ℝ → C₀(V,ℂ)) (t : ℝ) (x : V) : ℂ :=
  physicalForce γ f t x-(physicalPrincipal Af t x : ℂ)*Δ (Δ (fun y => physical γ v t y)) x-
    (physicalPotential Bf t x : ℂ)*physical γ v t x

theorem exists_finite_physical_inverse (c : ℝ) (Af Bf : V → ℝ)
    (h : SymbolBounds c Af Bf) (hAf : Radial Af) (hBf : Radial Bf) :
    ∃ γ : ℝ, 0<γ ∧ γ<1/2 ∧
    ∃ D : (ℝ →ᵇ C₀(V,ℂ)) →L[ℂ] (ℝ →ᵇ C₀(V,ℂ)),
      (∀ α a M : ℝ, 0<α → α<1 → 0<a → 0≤M → ∀ f : ℝ →ᵇ C₀(V,ℂ),
        (∀ s : ℝ, ∃ H : ℝ, 0≤H ∧ ∀ t ∈ Icc s (s+1), ∀ x y,
          ‖f t x-f t y‖≤H*‖x-y‖^α) →
        YBound α (-2+4*γ) a M (fun p : V × ℝ => physicalForce γ f p.2 p.1) →
        (∀ t : ℝ, ContDiff ℝ 4 (fun x => physical γ (D f) t x)) ∧
        (∀ t : ℝ, t<0 → ∀ x : V,
          HasDerivAt (fun r => physical γ (D f) r x) (physicalTime γ Af Bf f (D f) t x) t) ∧
        LocallyFiniteJets α (fun t x => physical γ (D f) t x) (physicalTime γ Af Bf f (D f))) ∧
      (∀ f : ℝ →ᵇ C₀(V,ℂ), ∀ t : ℝ, ∀ x : V,
        ‖physical γ (D f) t x‖≤‖D‖*‖f‖*Real.exp ((1/2-γ)*similarityTime t)) ∧
      (∀ f : ℝ →ᵇ C₀(V,ℂ), (∀ τ, Radial (f τ : V → ℂ)) →
        ∀ t, Radial (physical γ (D f) t : V → ℂ)) ∧
      (∀ f : ℝ →ᵇ C₀(V,ℂ), (∀ τ, RealValued (f τ : V → ℂ)) →
        ∀ t, RealValued (physical γ (D f) t : V → ℂ)) := by
  obtain ⟨γ,hγ,hγ1,S,h0,hc,ha,hE,D,hD,hRad,hReal⟩ :=
    exists_preliminary_ancient_inverse c Af Bf h hAf hBf
  obtain ⟨K,hK,hKb⟩ := AncientMild.bounded_on S hc 1
  refine ⟨γ,hγ,hγ1,D,?_,?_,?_,?_⟩
  · intro α a M hα hα1 ha' hM f hf hY
    have hw (s : ℝ) := classical_window c Af Bf h S h0 hc ⟨K,hKb⟩ ha hE γ hγ.le
      f (D f) (hD f) α hα hα1.le s (hf s)
    have hs : (1/2 : ℝ)∈Ioo (0:ℝ) 1 := by constructor <;> norm_num
    have hreg (τ : ℝ) : ContDiff ℝ 4 (fun x => D f τ x) := by
      obtain ⟨u,hu,hue⟩ := hw (τ-1/2)
      have he : renormalized γ u (1/2)=D f τ := by
        simpa only [sub_add_cancel] using hue (1/2) ⟨hs.1.le,hs.2.le⟩
      rw [←he]
      exact hu.renormalized_contDiff γ hs
    have hr := physical_contDiff γ (D f) hreg
    have hd (t : ℝ) (ht : t<0) (x : V) :
        HasDerivAt (fun r => physical γ (D f) r x) (physicalTime γ Af Bf f (D f) t x) t := by
      obtain ⟨u,hu,hue⟩ := hw (similarityTime t-1/2)
      exact physical_deriv_of_window Af Bf γ (similarityTime t-1/2) hγ.le f (D f) u hu hue ht
        (by simpa only [sub_sub_cancel] using hs) x
    refine ⟨hr,hd,?_⟩
    apply physical_locally_finite α γ (-2+4*γ) a M hα hα1 (by linarith) ha' hM
      Af Bf (h.2.2.1.of_le (by simp)) (h.2.2.2.1.of_le (by simp)) (D f)
      (physicalTime γ Af Bf f (D f)) _ hY (fun t _ => hr t) hd
    · intro t ht x
      dsimp [physicalTime]
      ring
    · intro p hp
      apply physical_fourth_local γ α hα hα1 (D f) _ p hp
      intro s
      obtain ⟨u,hu,hue⟩ := hw s
      refine ⟨u,hu.2.2.1,hue,?_⟩
      exact hu.fourth_holder c Af Bf h α hα hα1 (FlatSimilarity.normalizedSource γ s hγ.le f)
        (normalizedSource_holder γ s α hγ.le f (hf s)) (D f s) u (1/4) (by norm_num)
  · intro f t x
    have hb : ‖D f (similarityTime t) (Real.exp (similarityTime t/4) • x)‖≤‖D‖*‖f‖ :=
      ((D f (similarityTime t)).toBCF.norm_coe_le_norm _).trans
        (((D f).norm_coe_le_norm _).trans (D.le_opNorm f))
    rw [physical_apply,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ Real.exp ((1/2-γ)*similarityTime t)*(‖D‖*‖f‖) :=
        mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
      _ = _ := by ring
  · intro f hf t R x
    simp only [physical_apply,←R.map_smul]
    rw [hRad f hf (similarityTime t) R]
  · intro f hf t x
    simp only [physical_apply,star_mul,Complex.star_def,Complex.conj_ofReal]
    simpa only [Complex.star_def,mul_comm] using congrArg (fun z : ℂ => (Real.exp ((1/2-γ)*similarityTime t) : ℂ)*z)
      (hReal f hf (similarityTime t) (Real.exp (similarityTime t/4) • x))
end FlatSimilarity

end

end OAI
