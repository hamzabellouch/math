import Mathlib
import OAI.Analysis.BiholderTransport.Regularity.FiniteIntervalMesh
import OAI.Analysis.BiholderTransport.LinearAlgebra.ShearedSpectrum
import OAI.Analysis.BiholderTransport.LinearAlgebra.ConvexSpectrum
import OAI.Analysis.BiholderTransport.Regularity.SingularValuesBound

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff

namespace WeakMTWTransport
section EndpointSpectrumBound
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
local instance (x : M) : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))

lemma uniform_endpoint_singular_bound :
    ∃ D : ℝ, 0<D ∧ ∀ x : M, ∀ p : TangentSpace 𝓘(ℝ,Model n) x,
      p∈minimizingVectors x → ∀ i : Fin (Module.finrank ℝ (Model n)),
      (endpointExpDifferential x p).toLinearMap.singularValues i ≤ D := by
  obtain ⟨a,b,ha,hb,H⟩ := uniform_radial_singular_shortening (n := n) (M := M)
  obtain ⟨l,u,hl,hu,J⟩ := uniform_split_exp_bounds (n := n) (M := M)
  refine ⟨u/a,div_pos hu ha,?_⟩
  intro x p hp i
  have hj := (J (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M) hp (1/2)
    (by constructor <;> norm_num)).1
  have hj' : ∀ v : TangentSpace 𝓘(ℝ,Model n) x,
      ‖endpointExpDifferential x ((1/2:ℝ) • p) v‖ ≤ u*‖v‖ := fun v => by
    exact (hj v).2
  have hS := singularValues_le_of_bound (E := TangentSpace 𝓘(ℝ,Model n) x)
    (F := TangentSpace 𝓘(ℝ,Model n) (riemannianExp x ((1/2:ℝ) • p))) (endpointExpDifferential x ((1/2:ℝ) • p)).toLinearMap
    hu.le hj' rfl i
  have hR := (H x p hp (1/2) (by constructor <;> norm_num) i).1
  rw [show (1:ℝ)-1/2=1/2 by norm_num] at hR
  have HH := hR.trans hS
  rw [le_div_iff₀ ha]
  nlinarith only [HH,ha]
end EndpointSpectrumBound
end WeakMTWTransport

end

end

section

noncomputable section
open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff

namespace WeakMTWTransport
section AffineSpectrum
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
local instance (x : M) : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))

lemma WeakMTW.uniform_extended_spectral_comparison
    (hmtw : WeakMTW (n := n) (M := M)) {a₀ B : ℝ} (ha₀ : 0<a₀) (hB : 0<B) :
    ∃ c : ℝ, 0<c ∧ ∀ x : M, ∀ p q : TangentSpace 𝓘(ℝ,Model n) x,
      0 < inner ℝ p q → ‖q‖^2/inner ℝ p q ≤ B →
      (∀ t∈Icc (-a₀) 1, p+t • q∈minimizingVectors x) →
      ∀ i : Fin (Module.finrank ℝ (Model n)),
      c*(endpointExpDifferential x (p+q)).toLinearMap.singularValues i ≤
        (endpointExpDifferential x p).toLinearMap.singularValues i := by
  let a := min a₀ (1/(2*B))
  have ha : 0<a := lt_min ha₀ (div_pos (by norm_num) (by positivity))
  have haB : a*B ≤ 1/2 := by
    have HH := min_le_right a₀ (1/(2*B))
    have HH2 := (le_div_iff₀ (show 0<2*B by positivity)).mp HH
    nlinarith only [HH2]
  obtain ⟨l,u,b,hl,hu,hb,HSp⟩ := uniform_sheared_radial_spectrum (n := n) (M := M) ha hB haB
  obtain ⟨C,hC,HB⟩ := uniform_sheared_radial_quadratic_bounds (n := n) (M := M) ha hB haB
  obtain ⟨D,hD,HD⟩ := uniform_endpoint_singular_bound (n := n) (M := M)
  let e := min (1/2:ℝ) (l/(64*C))
  have he0 : 0<e := lt_min (by norm_num) (div_pos hl (by positivity))
  have he1 : e<1 := (min_le_left _ _).trans_lt (by norm_num)
  have heC : e*C ≤ l/32 := by
    have HH := (le_div_iff₀ (show 0<64*C by positivity)).mp
      (min_le_right (1/2:ℝ) (l/(64*C)))
    change e*(64*C) ≤ l at HH
    nlinarith only [HH,hl]
  let d := min a e
  have hdpos : 0<d := lt_min ha he0
  let K := 2*C/d
  have hK : 0 ≤ K := div_nonneg (by positivity) hdpos.le
  obtain ⟨c,hc,HC⟩ := uniform_finite_profile_comparison hC hl hu hb hD ⟨he0,he1⟩ heC hK
  refine ⟨c,hc,?_⟩
  intro x p q hpq hβ hline₀ j
  have hline (t : ℝ) (ht : t∈Icc (-a) 1) : p+t • q∈minimizingVectors x :=
    hline₀ t ⟨by have := min_le_left a₀ (1/(2*B)); change a ≤ a₀ at this; linarith [ht.1],ht.2⟩
  let i := j.rev
  let s : ℝ → ℝ := fun t => (endpointExpDifferential x (p+t • q)).toLinearMap.singularValues i.rev
  have hSym (δ : ℝ) (hd : δ∈Ioc (0:ℝ) (1/2)) (t : ℝ) (ht : t∈Icc (-a) 1) :
      (shearedRadialOperator x p q δ t).toLinearMap.IsSymmetric :=
    shearedRadialOperator_symmetric (contracted_minimizer_mem_injectivityDomain (hline t ht)
      (by linarith [hd.2]) (by linarith [hd.1]))
  let f : ℝ → ℝ → ℝ := fun δ t =>
    if H : δ∈Ioc (0:ℝ) (1/2) ∧ t∈Icc (-a) 1 then (hSym δ H.1 t H.2).eigenvalues rfl i else 0
  have hf (δ : ℝ) (hd : δ∈Ioc (0:ℝ) (1/2)) (t : ℝ) (ht : t∈Icc (-a) 1) :
      f δ t=(hSym δ hd t ht).eigenvalues rfl i := by
    dsimp only [f]
    rw [dite_eq_left (show δ∈Ioc (0:ℝ) (1/2) ∧ t∈Icc (-a) 1 from ⟨hd,ht⟩)]
  have hI (t : ℝ) (ht : t∈Icc (0:ℝ) 1) : t∈Icc (-a) 1 := ⟨by linarith [ht.1],ht.2⟩
  have hSmall (t : ℝ) (ht : t∈Icc (0:ℝ) (1-e)) : t∈Icc (0:ℝ) 1 :=
    ⟨ht.1,by linarith [ht.2]⟩
  have hInt (t : ℝ) (ht : t∈Icc (0:ℝ) (1-e)) : t∈Icc (-a+d) (1-d) := by
    have hda : d ≤ a := min_le_left _ _
    have hde : d ≤ e := min_le_right _ _
    constructor <;> linarith [ht.1,ht.2]
  have h0 : (0:ℝ)∈Icc (-a) 1 := ⟨by linarith,by norm_num⟩
  have h1 : (1:ℝ)∈Icc (-a) 1 := ⟨by linarith,le_rfl⟩
  have hm : 1-e∈Icc (-a) 1 := ⟨by linarith,by linarith⟩
  have HS (t : ℝ) (ht : t∈Icc (0:ℝ) 1) : 0 ≤ s t :=
    (endpointExpDifferential x (p+t • q)).toLinearMap.singularValues_nonneg i.rev
  have HD' : s 1 ≤ D := HD x (p+1 • q) (hline 1 h1) i.rev
  have HP (δ : ℝ) (hd : δ∈Ioc (0:ℝ) (1/2)) (t : ℝ) (ht : t∈Icc (0:ℝ) 1) :
      l*δ/(s t+δ)-b*δ ≤ f δ t ∧ f δ t ≤ u*δ/(s t+δ)+b*δ := by
    obtain ⟨hF,H⟩ := HSp x p q hpq hβ hline δ hd t (hI t ht)
    rw [hf δ hd t (hI t ht)]
    exact H i
  have HL (δ : ℝ) (hd : δ∈Ioc (0:ℝ) (1/2)) (r : ℝ) (hr : r∈Icc (0:ℝ) (1-e))
      (t : ℝ) (ht : t∈Icc (0:ℝ) (1-e)) : |f δ t-f δ r| ≤ K*|t-r| := by
    rw [hf δ hd t (hI t (hSmall t ht)),hf δ hd r (hI r (hSmall r hr))]
    exact bounded_matrix_convex_eigen_secant (hSym δ hd)
      (hmtw.shearedRadialOperator_convexOn x p q hpq.ne' hd hline) hC.le hdpos
      (fun t ht v => (HB x p q hpq hβ hline δ hd t ht v).2)
      (hInt r hr) (hInt t ht) (hI r (hSmall r hr)) (hI t (hSmall t ht)) rfl i
  have HE (δ : ℝ) (hd : δ∈Ioc (0:ℝ) (1/2)) : f δ (1-e) ≤ (1-e)*f δ 1+e*C := by
    rw [hf δ hd (1-e) hm,hf δ hd 1 h1]
    exact matrix_convex_eigen_endpoint ha.le ⟨he0.le,he1.le⟩ (hSym δ hd)
      (hmtw.shearedRadialOperator_convexOn x p q hpq.ne' hd hline)
      (fun v => (le_abs_self _).trans (HB x p q hpq hβ hline δ hd 0 h0 v).2) hm h1 rfl i
  have result := HC s f HS HD' HP HL HE
  have hz : p+(0:ℝ) • q=p := by simp
  have ho : p+(1:ℝ) • q=p+q := by simp
  have hsz : s 0=(endpointExpDifferential x p).toLinearMap.singularValues j := by
    change (endpointExpDifferential x (p+(0:ℝ) • q)).toLinearMap.singularValues i.rev=_
    rw [hz,show i.rev=j from Fin.rev_rev j]
  have hso : s 1=(endpointExpDifferential x (p+q)).toLinearMap.singularValues j := by
    change (endpointExpDifferential x (p+(1:ℝ) • q)).toLinearMap.singularValues i.rev=_
    rw [ho,show i.rev=j from Fin.rev_rev j]
  rwa [hsz,hso] at result
end AffineSpectrum
end WeakMTWTransport

end

end

end

end OAI
