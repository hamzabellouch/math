import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.ParametricSmooth01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
noncomputable section
open scoped BigOperators Topology
open Filter
end
 
end

section
 

 

noncomputable section
open scoped BigOperators Topology
open Filter
universe u
namespace AllLevelRemovals
open RationalLattice
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {n s : ℕ} {c : RealCoordinates G n} {L : ℕ → ℝ}

namespace Removal

def smooth (w : Removal c L s) (N : ℕ) (b : ℝ) : G :=
  w.flow (Multiplicative.ofAdd (w.small N*Ring.choose b w.degree))

omit [IsTopologicalGroup G] in
lemma smooth_integer [IsTopologicalGroup G] (w : Removal c L s) (N : ℕ) (z : ℤ) :
    w.smooth N (z:ℝ)=w.left N z := by
  have hc:=Ring.map_choose (Int.castRingHom ℝ) z w.degree
  change ((Ring.choose z w.degree:ℤ):ℝ)=Ring.choose (z:ℝ) w.degree at hc
  rw [smooth,← hc,left,← w.flow.map_zpow]
  congr 1
  change Multiplicative.ofAdd (w.small N* ((Ring.choose z w.degree:ℤ):ℝ))=
    Multiplicative.ofAdd ((Ring.choose z w.degree:ℤ) • w.small N)
  simp only [zsmul_eq_mul,mul_comm]

end Removal

def smoothWord (W : List (Removal c L s)) (N : ℕ) (b : ℝ) : G :=
  (W.map (fun w=>w.smooth N b)).prod
lemma smoothWord_integer (W : List (Removal c L s)) (N : ℕ) (z : ℤ) :
    smoothWord W N (z:ℝ)=leftWord W N z := by
  simp [smoothWord,leftWord,Removal.smooth_integer]

section Parameters
variable {l : ℕ} (W : Fin l → Removal c L s)

def scalarProfile (i : Fin l) (t : Option (Fin l) → ℝ) (x : ℝ) : ℝ :=
  t (some i) * ((W i).degree.factorial:ℝ)⁻¹ *
    ∏ k∈Finset.range (W i).degree,(x-(k:ℝ)*t none)

def profile (t : Option (Fin l) → ℝ) (x : ℝ) : G :=
  (List.ofFn (fun i=>(W i).flow (Multiplicative.ofAdd (scalarProfile W i t x)))).prod

def parameters (N : ℕ) : Option (Fin l) → ℝ
  | none => (L N)⁻¹
  | some i => (L N)^(W i).degree*(W i).small N

def limitParameters : Option (Fin l) → ℝ
  | none => 0
  | some i => (W i).limit

omit [IsTopologicalGroup G] in
lemma parameters_tendsto [IsTopologicalGroup G] (hL : Tendsto L atTop atTop) :
    Tendsto (parameters W) atTop (𝓝 (limitParameters W)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  cases i with
  | none => exact tendsto_inv_atTop_zero.comp hL
  | some i => exact (W i).scaled_tendsto

omit [IsTopologicalGroup G] in
lemma scalarProfile_parameters [IsTopologicalGroup G] (N : ℕ) (hL : L N≠0) (i : Fin l) (x : ℝ) :
    scalarProfile W i (parameters W N) x=(W i).small N*Ring.choose (L N*x) (W i).degree := by
  rw [SmoothBinomial.amplitude_identity _ _ _ _ hL,SmoothBinomial.universal_eval]
  simp only [scalarProfile,parameters]
  ring

omit [IsTopologicalGroup G] in
lemma scalarProfile_limit [IsTopologicalGroup G] (i : Fin l) (x : ℝ) :
    scalarProfile W i (limitParameters W) x=
      (W i).limit *((W i).degree.factorial:ℝ)⁻¹*x^(W i).degree := by
  simp [scalarProfile,limitParameters]

omit [IsTopologicalGroup G] in
lemma scalarProfile_polynomial [IsTopologicalGroup G] (i : Fin l) : ParametricSmooth.IsPolynomial (scalarProfile W i) := by
  unfold scalarProfile
  exact ParametricSmooth.mul
    (ParametricSmooth.mul (ParametricSmooth.parameter (some i)) (ParametricSmooth.constant _))
    (ParametricSmooth.finite_prod _ (fun k _=>ParametricSmooth.sub ParametricSmooth.coordinate
      (ParametricSmooth.mul (ParametricSmooth.constant _) (ParametricSmooth.parameter none))))

omit [IsTopologicalGroup G] in
lemma polynomial_mul [IsTopologicalGroup G] {σ : Type*} {f g : (σ → ℝ) → ℝ → G}
    (hf : ∀ i,ParametricSmooth.IsPolynomial (fun t x=>c.coord (f t x) i))
    (hg : ∀ i,ParametricSmooth.IsPolynomial (fun t x=>c.coord (g t x) i)) :
    ∀ i,ParametricSmooth.IsPolynomial (fun t x=>c.coord (f t x*g t x) i) := by
  intro i
  simp only [c.mul_coord]
  refine ParametricSmooth.add (ParametricSmooth.add (hf i) (hg i)) ?_
  apply ParametricSmooth.mvpolynomial_eval
  intro j
  cases j with
  | inl j => exact hf _
  | inr j => exact hg _

lemma profile_polynomial (i : Fin n) :
    ParametricSmooth.IsPolynomial (fun t x=>c.coord (profile W t x) i) := by
  have hflow (a : Fin l) (i : Fin n) : ParametricSmooth.IsPolynomial
      (fun t x=>c.coord ((W a).flow (Multiplicative.ofAdd (scalarProfile W a t x))) i) := by
    have he (t : Option (Fin l) → ℝ) (x : ℝ) :
        c.coord ((W a).flow (Multiplicative.ofAdd (scalarProfile W a t x))) i=
          (powerPolynomial c ((W a).flow (Multiplicative.ofAdd 1)) i).eval (scalarProfile W a t x) := by
      rw [RationalLevelFlow.continuous_flow_eq_realPower c (W a).flow (W a).continuous
        (scalarProfile W a t x),realPower_coord]
    simp_rw [he]
    exact ParametricSmooth.polynomial_eval _ (scalarProfile_polynomial W a)
  unfold profile
  simp only [List.ofFn_eq_map]
  generalize List.finRange l=v
  induction v generalizing i with
  | nil => simpa [c.one_coord] using ParametricSmooth.constant (σ:=Option (Fin l)) 0
  | cons a v ih =>
    simp only [List.map_cons,List.prod_cons]
    exact polynomial_mul (fun i=>hflow a i) (fun i=>by
      exact ih i) i

lemma profile_smooth (t : Option (Fin l) → ℝ) (i : Fin n) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x=>c.coord (profile W t x) i) := by
  obtain ⟨p,hp⟩:=profile_polynomial W i
  have he : (fun x=>c.coord (profile W t x) i)=fun x=>(ParametricSmooth.family p t).eval x:=
    funext (fun x=>(hp t x).symm)
  rw [he]
  simp only [Polynomial.eval_eq_sum_range]
  fun_prop

end Parameters

def smoothLimit (W : List (Removal c L s)) (x : ℝ) : G :=
  profile W.get (limitParameters W.get) x

lemma smoothWord_eq_profile (W : List (Removal c L s)) (N : ℕ) (hL : L N≠0) (x : ℝ) :
    smoothWord W N (L N*x)=profile W.get (parameters W.get N) x := by
  unfold smoothWord profile
  simp_rw [scalarProfile_parameters W.get N hL]
  rw [List.ofFn_eq_map]
  conv_lhs => rw [← List.map_get_finRange W,List.map_map]
  rfl

 

theorem smoothWord_limit (W : List (Removal c L s))
    (hL : ∀ N,0<L N) (ht : Tendsto L atTop atTop)
    (k : ℕ) (i : Fin n) (K : Set ℝ) (hK : IsCompact K) :
    TendstoUniformlyOn (fun N=>iteratedDeriv k (fun x=>c.coord (smoothWord W N (L N*x)) i))
      (iteratedDeriv k (fun x=>c.coord (smoothLimit W x) i)) atTop K := by
  simp_rw [smoothWord_eq_profile W _ (ne_of_gt (hL _))]
  exact ParametricSmooth.compact_derivative_limit (profile_polynomial W.get i)
    (parameters_tendsto W.get ht) k K hK

 

theorem smoothWord_bounds (W : List (Removal c L s))
    (hL : ∀ N,0<L N) (ht : Tendsto L atTop atTop)
    (k : ℕ) (i : Fin n) (K : Set ℝ) (hK : IsCompact K) :
    ∃ B>0,∀ N x,x∈K →
      |iteratedDeriv k (fun x=>c.coord (smoothWord W N (L N*x)) i) x|≤B := by
  simp_rw [smoothWord_eq_profile W _ (ne_of_gt (hL _))]
  exact ParametricSmooth.compact_derivative_bound (profile_polynomial W.get i)
    (parameters_tendsto W.get ht) k K hK

end AllLevelRemovals
end
 
end

section
 

 

noncomputable section
open scoped BigOperators Topology
open Filter
universe u
namespace AllLevelRemovals
open RationalLattice
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {n s : ℕ} {c : RealCoordinates G n} {L : ℕ → ℝ}
variable {l : ℕ} (W : Fin l → Removal c L s)

def prefixProfile (t : (Fin n ⊕ Option (Fin l)) → ℝ) (x : ℝ) : G :=
  c.coord.symm (t∘Sum.inl)*profile W (t∘Sum.inr) x

lemma prefixProfile_polynomial (i : Fin n) :
    ParametricSmooth.IsPolynomial (fun t x=>c.coord (prefixProfile W t x) i) := by
  apply polynomial_mul
  · intro j
    simpa only [Homeomorph.apply_symm_apply,Function.comp_apply] using
      ParametricSmooth.parameter (Sum.inl j : Fin n ⊕ Option (Fin l))
  · intro j
    exact ParametricSmooth.rename_parameters (profile_polynomial W j) Sum.inr

def prefixParameters (a : ℕ → G) (N : ℕ) : (Fin n ⊕ Option (Fin l)) → ℝ :=
  Sum.elim (c.coord (a N)) (parameters W N)
def prefixLimitParameters (a₀ : G) : (Fin n ⊕ Option (Fin l)) → ℝ :=
  Sum.elim (c.coord a₀) (limitParameters W)

lemma prefixParameters_tendsto {a : ℕ → G} {a₀ : G} (ha : Tendsto a atTop (𝓝 a₀))
    (hL : Tendsto L atTop atTop) :
    Tendsto (prefixParameters W a) atTop (𝓝 (prefixLimitParameters W a₀)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  cases i with
  | inl i => exact ((continuous_apply i).comp c.coord.continuous).continuousAt.tendsto.comp ha
  | inr i => exact (tendsto_pi_nhds.mp (parameters_tendsto W hL)) i

omit [IsTopologicalGroup G] in
lemma prefixProfile_parameters [IsTopologicalGroup G] (a : ℕ → G) (N : ℕ) (x : ℝ) :
    prefixProfile W (prefixParameters W a N) x=a N*profile W (parameters W N) x := by
  simp [prefixProfile,prefixParameters,Function.comp_def]
omit [IsTopologicalGroup G] in
lemma prefixProfile_limit [IsTopologicalGroup G] (a₀ : G) (x : ℝ) :
    prefixProfile W (prefixLimitParameters W a₀) x=a₀*profile W (limitParameters W) x := by
  simp [prefixProfile,prefixLimitParameters,Function.comp_def]

theorem prefix_smoothWord_limit (V : List (Removal c L s))
    (hL : ∀ N,0<L N) (ht : Tendsto L atTop atTop)
    {a : ℕ → G} {a₀ : G} (ha : Tendsto a atTop (𝓝 a₀))
    (k : ℕ) (i : Fin n) (K : Set ℝ) (hK : IsCompact K) :
    TendstoUniformlyOn (fun N=>iteratedDeriv k (fun x=>c.coord (a N*smoothWord V N (L N*x)) i))
      (iteratedDeriv k (fun x=>c.coord (a₀*smoothLimit V x) i)) atTop K := by
  have h:=ParametricSmooth.compact_derivative_limit (prefixProfile_polynomial V.get i)
    (prefixParameters_tendsto V.get ha ht) k K hK
  simp_rw [prefixProfile_parameters,prefixProfile_limit] at h
  simp_rw [smoothWord_eq_profile V _ (ne_of_gt (hL _))]
  exact h

theorem prefix_smoothWord_bounds (V : List (Removal c L s))
    (hL : ∀ N,0<L N) (ht : Tendsto L atTop atTop)
    {a : ℕ → G} {a₀ : G} (ha : Tendsto a atTop (𝓝 a₀))
    (k : ℕ) (i : Fin n) (K : Set ℝ) (hK : IsCompact K) :
    ∃ B>0,∀ N x,x∈K →
      |iteratedDeriv k (fun x=>c.coord (a N*smoothWord V N (L N*x)) i) x|≤B := by
  have h:=ParametricSmooth.compact_derivative_bound (prefixProfile_polynomial V.get i)
    (prefixParameters_tendsto V.get ha ht) k K hK
  simp_rw [prefixProfile_parameters] at h
  simp_rw [smoothWord_eq_profile V _ (ne_of_gt (hL _))]
  exact h

theorem prefix_smoothLimit_smooth (V : List (Removal c L s)) (a₀ : G) (i : Fin n) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x=>c.coord (a₀*smoothLimit V x) i) := by
  obtain ⟨p,hp⟩:=prefixProfile_polynomial V.get i
  have he : (fun x=>c.coord (a₀*smoothLimit V x) i)=
      fun x=>(ParametricSmooth.family p (prefixLimitParameters V.get a₀)).eval x := by
    funext x
    simpa only [prefixProfile_limit,smoothLimit] using (hp (prefixLimitParameters V.get a₀) x).symm
  rw [he]
  simp only [Polynomial.eval_eq_sum_range]
  fun_prop

end AllLevelRemovals

end
end
end
end

end OAI
