import OAI.Dynamics.SmoothObstruction.ShortDerivative

namespace OAI

section

open MeasureTheory Filter Topology TopologicalSpace Set Finset
open scoped ENNReal NNReal BoundedContinuousFunction
open Finset MeasureTheory Filter Topology
open scoped BigOperators
open Finset Matrix
open scoped Matrix.Norms.L2Operator
open Matrix

namespace SmoothObstruction.EuclideanSplitting
open scoped Matrix.Norms.L2Operator
variable {d : ℕ}

noncomputable def gaugeEquiv (U V : Matrix (Fin d) (Fin d) ℝ)
    (hUV : U*V=1) (hVU : V*U=1) :
    EuclideanSpace ℝ (Fin d) ≃L[ℝ] EuclideanSpace ℝ (Fin d) :=
  (LinearEquiv.ofLinearMap
    (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) U).toLinearMap
    (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) V).toLinearMap
    (by
      apply LinearMap.ext
      intro x
      change Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) U
        (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) V x)=x
      rw [←mul_apply_eq_comp,←map_mul,hUV,map_one]
      rfl)
    (by
      apply LinearMap.ext
      intro x
      change Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) V
        (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) U x)=x
      rw [←mul_apply_eq_comp,←map_mul,hVU,map_one]
      rfl)).toContinuousLinearEquiv

@[simp] lemma gaugeEquiv_apply (U V : Matrix (Fin d) (Fin d) ℝ)
    (hUV : U*V=1) (hVU : V*U=1) (x : EuclideanSpace ℝ (Fin d)) :
    gaugeEquiv U V hUV hVU x=Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) U x := rfl

@[simp] lemma gaugeEquiv_symm_apply (U V : Matrix (Fin d) (Fin d) ℝ)
    (hUV : U*V=1) (hVU : V*U=1) (x : EuclideanSpace ℝ (Fin d)) :
    (gaugeEquiv U V hUV hVU).symm x=Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) V x := rfl

noncomputable def coordinateSpace (S : Finset (Fin d)) :
    Submodule ℝ (EuclideanSpace ℝ (Fin d)) :=
  (Pi.spanSubset ℝ (S:Set (Fin d))).map (WithLp.linearEquiv 2 ℝ (Fin d→ℝ)).symm.toLinearMap

lemma mem_coordinateSpace (S : Finset (Fin d)) (x : EuclideanSpace ℝ (Fin d)) :
    x∈coordinateSpace S ↔ ∀ j∉S,x j=0 := by
  rw [coordinateSpace,Submodule.map_equiv_eq_comap_symm]
  exact Pi.mem_spanSubset_iff

lemma finrank_coordinateSpace (S : Finset (Fin d)) :
    Module.finrank ℝ (coordinateSpace S)=S.card := by
  rw [coordinateSpace,LinearEquiv.finrank_map_eq,Pi.dim_spanSubset,Set.ncard_coe_finset]

lemma mask_apply (S : Finset (Fin d)) (x : EuclideanSpace ℝ (Fin d)) (j : Fin d) :
    (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (mask S) x) j=if j∈S then x j else 0 := by
  change ((mask S)*ᵥ (WithLp.ofLp x)) j=_
  rw [mask,Matrix.mulVec_diagonal]
  split <;> simp_all

lemma coordinateSpace_fixed (S : Finset (Fin d)) (x : EuclideanSpace ℝ (Fin d)) :
    x∈coordinateSpace S ↔ Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (mask S) x=x := by
  rw [mem_coordinateSpace]
  constructor
  · intro hx
    ext j
    rw [mask_apply]
    split_ifs with hj
    · rfl
    · exact (hx j hj).symm
  · intro hx j hj
    have he := congrArg (fun x : EuclideanSpace ℝ (Fin d) => x j) hx
    rw [mask_apply,ite_eq_right hj] at he
    exact he.symm

noncomputable def groupSpace (U V : Matrix (Fin d) (Fin d) ℝ)
    (hUV : U*V=1) (hVU : V*U=1) (S : Finset (Fin d)) :
    Submodule ℝ (EuclideanSpace ℝ (Fin d)) :=
  (coordinateSpace S).map (gaugeEquiv U V hUV hVU).toLinearEquiv.toLinearMap

lemma finrank_groupSpace (U V : Matrix (Fin d) (Fin d) ℝ)
    (hUV : U*V=1) (hVU : V*U=1) (S : Finset (Fin d)) :
    Module.finrank ℝ (groupSpace U V hUV hVU S)=S.card := by
  rw [groupSpace,LinearEquiv.finrank_map_eq,finrank_coordinateSpace]

lemma groupSpace_fixed (U V : Matrix (Fin d) (Fin d) ℝ)
    (hUV : U*V=1) (hVU : V*U=1) (S : Finset (Fin d))
    (x : EuclideanSpace ℝ (Fin d)) :
    x∈groupSpace U V hUV hVU S ↔
      Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (U*mask S*V) x=x := by
  rw [groupSpace,Submodule.map_equiv_eq_comap_symm]
  change (gaugeEquiv U V hUV hVU).symm x∈coordinateSpace S ↔ _
  rw [coordinateSpace_fixed]
  constructor
  · intro hx
    have he := congrArg (gaugeEquiv U V hUV hVU) hx
    rw [(gaugeEquiv U V hUV hVU).apply_symm_apply] at he
    simpa only [gaugeEquiv_apply,gaugeEquiv_symm_apply,map_mul,
      mul_apply_eq_comp] using he
  · intro hx
    apply (gaugeEquiv U V hUV hVU).injective
    rw [(gaugeEquiv U V hUV hVU).apply_symm_apply]
    simpa only [gaugeEquiv_apply,gaugeEquiv_symm_apply,map_mul,
      mul_apply_eq_comp] using hx

end SmoothObstruction.EuclideanSplitting

namespace SmoothObstruction.EuclideanSplitting
open scoped Matrix.Norms.L2Operator
variable {d : ℕ}

lemma groupSpace_forward (U V : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (hUV : ∀ t,U t*V t=1) (hVU : ∀ t,V t*U t=1) (lam : Fin d → ℝ)
    (S : Finset (Fin d)) {K c : ℝ} {s t : ℕ} (hst : s≤t)
    (hU : ‖U t‖≤Real.exp K) (hV : ‖V s‖≤Real.exp K)
    (hc : ∀ j∈S,lam j≤c) (x : groupSpace (U s) (V s) (hUV s) (hVU s) S) :
    ‖Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (transition U V lam s t) x‖ ≤
      Real.exp (c*((t:ℝ)-s)+2*K)*‖x‖ := by
  have hx := (groupSpace_fixed (U s) (V s) (hUV s) (hVU s) S x).mp x.property
  have hb := norm_transition_projection U V hVU lam S s t hst hU hV hc
  have hn := (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)
    (transition U V lam s t*projection U V S s)).le_opNorm (x:EuclideanSpace ℝ (Fin d))
  rw [Matrix.l2_opNorm_toEuclideanCLM,map_mul,mul_apply_eq_comp] at hn
  change Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (projection U V S s) x=x at hx
  rw [hx] at hn
  exact hn.trans (mul_le_mul_of_nonneg_right hb (norm_nonneg _))

lemma inverse_fast_product (U V : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (hUV : ∀ t,U t*V t=1) (hVU : ∀ t,V t*U t=1) (lam : Fin d → ℝ)
    (S : Finset (Fin d)) (s t : ℕ) :
    (transition U V lam t s*projection U V S t)*transition U V lam s t=
      projection U V S s := by
  rw [mul_assoc,←transition_projection U V lam hVU,
    ←mul_assoc (transition U V lam t s),transition_comp U V lam hVU,
    transition_self U V lam hUV,one_mul]

lemma groupSpace_backward_lower (U V : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (hUV : ∀ t,U t*V t=1) (hVU : ∀ t,V t*U t=1) (lam : Fin d → ℝ)
    (S : Finset (Fin d)) {K c : ℝ} {s t : ℕ} (hst : s≤t)
    (hU : ‖U s‖≤Real.exp K) (hV : ‖V t‖≤Real.exp K)
    (hc : ∀ j∈S,c≤lam j) (x : groupSpace (U s) (V s) (hUV s) (hVU s) S) :
    Real.exp (c*((t:ℝ)-s)-2*K)*‖x‖ ≤
      ‖Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (transition U V lam s t) x‖ := by
  have hx := (groupSpace_fixed (U s) (V s) (hUV s) (hVU s) S x).mp x.property
  have hb := norm_backward_projection U V hVU lam S s t hst hU hV hc
  let P := Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (transition U V lam s t)
  let B := Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)
    (transition U V lam t s*projection U V S t)
  have hBP : B (P x)=x := by
    dsimp [B,P]
    rw [←mul_apply_eq_comp,←map_mul,inverse_fast_product U V hUV hVU]
    exact hx
  have hn := B.le_opNorm (P x)
  rw [hBP] at hn
  have hBn : ‖B‖≤Real.exp (-c*((t:ℝ)-s)+2*K) := by
    dsimp [B]
    rw [Matrix.l2_opNorm_toEuclideanCLM]
    exact hb
  have hxn : ‖(x:EuclideanSpace ℝ (Fin d))‖ ≤
      Real.exp (-c*((t:ℝ)-s)+2*K)*‖P x‖ :=
    hn.trans (mul_le_mul_of_nonneg_right hBn (norm_nonneg _))
  have hm := mul_le_mul_of_nonneg_left hxn (Real.exp_nonneg (c*((t:ℝ)-s)-2*K))
  have he : Real.exp (c*((t:ℝ)-s)-2*K)*Real.exp (-c*((t:ℝ)-s)+2*K)=1 := by
    rw [←Real.exp_add]
    rw [show (c*((t:ℝ)-s)-2*K)+(-c*((t:ℝ)-s)+2*K)=0 by ring,Real.exp_zero]
  rw [←mul_assoc,he,one_mul] at hm
  exact hm

end SmoothObstruction.EuclideanSplitting

namespace SmoothObstruction.SubspaceComparison
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- The elementary dimension/count comparison underlying finite singular
rate comparison. Actual operator closeness and stretch bounds force disjointness. -/
lemma disjoint_of_stretch (P Q : E →L[ℝ] E) (U V : Submodule ℝ E)
    {a b δ : ℝ} (hgap : b+δ<a) (hclose : ‖P-Q‖ ≤ δ)
    (hU : ∀ x : U, a*‖x‖ ≤ ‖P x‖) (hV : ∀ x : V, ‖Q x‖ ≤ b*‖x‖) :
    Disjoint U V := by
  rw [Submodule.disjoint_def]
  intro x hxU hxV
  have hu := hU ⟨x,hxU⟩
  have hv := hV ⟨x,hxV⟩
  change a*‖x‖ ≤ ‖P x‖ at hu
  change ‖Q x‖ ≤ b*‖x‖ at hv
  have hd : ‖P x-Q x‖ ≤ δ*‖x‖ :=
    ((P-Q).le_opNorm x).trans (mul_le_mul_of_nonneg_right hclose (norm_nonneg _))
  have ht : ‖P x‖ ≤ ‖P x-Q x‖+‖Q x‖ := by
    simpa only [sub_add_cancel] using norm_add_le (P x-Q x) (Q x)
  apply norm_eq_zero.mp
  nlinarith [norm_nonneg x]

lemma dimension_of_stretch (P Q : E →L[ℝ] E) (U V : Submodule ℝ E)
    {a b δ : ℝ} (hgap : b+δ<a) (hclose : ‖P-Q‖ ≤ δ)
    (hU : ∀ x : U, a*‖x‖ ≤ ‖P x‖) (hV : ∀ x : V, ‖Q x‖ ≤ b*‖x‖) :
    Module.finrank ℝ U+Module.finrank ℝ V ≤ Module.finrank ℝ E := by
  have hh := disjoint_of_stretch P Q U V hgap hclose hU hV
  have hd := Submodule.finrank_sup_add_finrank_inf_eq U V
  rw [hh.eq_bot, finrank_bot,add_zero] at hd
  rw [←hd]
  exact Submodule.finrank_le (U⊔V)

/-- Product comparison controls directed distance using an actual inverse
fast propagator B. K is the initial fast projector; its complementary image
lies in the reference slow space. -/
lemma directed_of_product (P Q B K : E →L[ℝ] E) (U V : Submodule ℝ E)
    {β σ δ : ℝ} (hβ : 0≤β)
    (hBP : B.comp P=K) (hB : ‖B‖≤β) (hclose : ‖P-Q‖≤δ)
    (hQ : ∀ x : U, ‖Q x‖≤σ*‖x‖)
    (hV : ∀ x, x-K x∈V) :
    ∀ x : U, ‖(x:E)-V.starProjection x‖ ≤ β*(σ+δ)*‖x‖ := by
  intro x
  have hPx : ‖P x‖ ≤ (σ+δ)*‖x‖ := by
    have hd : ‖P x-Q x‖ ≤ δ*‖x‖ :=
      ((P-Q).le_opNorm x).trans (mul_le_mul_of_nonneg_right hclose (norm_nonneg _))
    have ht := norm_add_le (Q x) (P x-Q x)
    rw [add_sub_cancel] at ht
    have hh := hQ x
    nlinarith
  have hKx : ‖K x‖ ≤ β*(σ+δ)*‖x‖ := by
    rw [←hBP,ContinuousLinearMap.comp_apply]
    calc
      _ ≤ ‖B‖*‖P x‖ := B.le_opNorm _
      _ ≤ β*((σ+δ)*‖x‖) := mul_le_mul hB hPx (norm_nonneg _) hβ
      _ = _ := by ring
  calc
    _ ≤ ‖(x:E)-((x:E)-K x)‖ := by
      rw [Submodule.starProjection_minimal]
      exact ciInf_le ⟨0, Set.forall_mem_range.mpr fun _ => norm_nonneg _⟩
        (⟨(x:E)-K x,hV x⟩:V)
    _ = ‖K x‖ := by rw [sub_sub_cancel]
    _ ≤ _ := hKx

end SmoothObstruction.SubspaceComparison

namespace SmoothObstruction.ShortBin
open EuclideanSplitting
open scoped Matrix.Norms.L2Operator

variable {d L : ℕ} {K : ℝ}

noncomputable def Gauge.product (A : Gauge d L K) :
    EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) :=
  Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (transition A.U A.V A.lam 0 L)

noncomputable def Gauge.space (A : Gauge d L K) (S : Finset (Fin d)) :
    Submodule ℝ (EuclideanSpace ℝ (Fin d)) :=
  groupSpace (A.U 0) (A.V 0) (A.UV 0) (A.VU 0) S

lemma Gauge.rank (A : Gauge d L K) (S : Finset (Fin d)) :
    Module.finrank ℝ (A.space S)=S.card :=
  finrank_groupSpace _ _ _ _ _

lemma Gauge.upper (A : Gauge d L K) (S : Finset (Fin d)) {c : ℝ}
    (hc : ∀ j∈S,A.lam j≤c) (x : A.space S) :
    ‖A.product x‖≤Real.exp (c*L+2*K)*‖x‖ := by
  convert! groupSpace_forward A.U A.V A.UV A.VU A.lam S (Nat.zero_le L)
      (A.normU L le_rfl) (A.normV 0 (Nat.zero_le L)) hc x using 1
  simp
  rfl

lemma Gauge.lower (A : Gauge d L K) (S : Finset (Fin d)) {c : ℝ}
    (hc : ∀ j∈S,c≤A.lam j) (x : A.space S) :
    Real.exp (c*L-2*K)*‖x‖≤‖A.product x‖ := by
  convert! groupSpace_backward_lower A.U A.V A.UV A.VU A.lam S (Nat.zero_le L)
      (A.normU 0 (Nat.zero_le L)) (A.normV L le_rfl) hc x using 1
  simp
  rfl

/-- A count comparison from actual product closeness. -/
lemma count_le (A B : Gauge d L K) {a b δ : ℝ}
    (hclose : ‖A.product-B.product‖≤δ)
    (hgap : Real.exp (b*L+2*K)+δ<Real.exp (a*L-2*K)) :
    (Finset.univ.filter (fun j => a≤A.lam j)).card ≤
      (Finset.univ.filter (fun j => b<B.lam j)).card := by
  classical
  let S := Finset.univ.filter (fun j => a≤A.lam j)
  let T := Finset.univ.filter (fun j => B.lam j≤b)
  have hd := SubspaceComparison.dimension_of_stretch A.product B.product (A.space S) (B.space T)
    hgap hclose (A.lower S (by intro j hj; exact (Finset.mem_filter.mp hj).2))
      (B.upper T (by intro j hj; exact (Finset.mem_filter.mp hj).2))
  rw [A.rank,B.rank,finrank_euclideanSpace_fin] at hd
  have he : (Finset.univ.filter (fun j => b<B.lam j))=Tᶜ := by
    ext j
    simp [T,not_le]
  have hc := Finset.card_add_card_compl T
  simp only [Fintype.card_fin] at hc
  rw [he]
  dsimp [S] at hd
  omega

lemma exponential_separation {K g δ c l : ℝ} (hc : 0≤c) (hl : 0≤l)
    (hdecay : Real.exp (-2*g*l+4*K)≤1/2)
    (hnoise : δ<Real.exp (-2*K)/2) :
    Real.exp ((c-2*g)*l+2*K)+δ<Real.exp (c*l-2*K) := by
  have he : Real.exp ((c-2*g)*l+2*K)=
      Real.exp (c*l-2*K)*Real.exp (-2*g*l+4*K) := by
    rw [←Real.exp_add]
    congr 1
    ring
  have ha : Real.exp (-2*K)≤Real.exp (c*l-2*K) :=
    Real.exp_le_exp.mpr (by nlinarith [mul_nonneg hc hl])
  have hb := mul_le_mul_of_nonneg_left hdecay (Real.exp_nonneg (c*l-2*K))
  rw [he]
  nlinarith

end SmoothObstruction.ShortBin

namespace SmoothObstruction.RateThreshold

/-- The manuscript's d+1 predetermined candidates. The choice is uniform over
all other witnesses once short-product comparison has been applied. -/
lemma exists_candidate (d : ℕ) (lam : Fin d → ℝ) {g : ℝ} (hg : 0<g) :
    ∃ j : Fin (d+1), ∀ i, 3*g < |lam i-(1+8*(j.val:ℝ))*g| := by
  classical
  by_contra! h
  choose f hf using h
  have hinj : Function.Injective f := by
    intro j k heq
    by_contra hne
    have hj := hf j
    have hk := hf k
    rw [←heq] at hk
    obtain hjlo := (abs_le.mp hj).1
    obtain hjhi := (abs_le.mp hj).2
    obtain hklo := (abs_le.mp hk).1
    obtain hkhi := (abs_le.mp hk).2
    have hv : j.val≠k.val := fun h => hne (Fin.ext h)
    rcases lt_or_gt_of_ne hv with hh | hh
    · have ha : (j.val:ℝ)+1≤k.val := by exact_mod_cast hh
      nlinarith
    · have ha : (k.val:ℝ)+1≤j.val := by exact_mod_cast hh
      nlinarith
  have hh := Fintype.card_le_of_injective f hinj
  simp only [Fintype.card_fin] at hh
  omega

/-- Two dimension comparisons exclude the whole intermediate rate band;
no singular-value decomposition or arbitrary sorted-rate choice is needed. -/
lemma of_sandwich {d p : ℕ} (lam : Fin d → ℝ) {γ g : ℝ} (hg : 0<g)
    (hlo : (Finset.univ.filter (fun j => γ-g≤lam j)).card≤p)
    (hhi : p≤(Finset.univ.filter (fun j => γ+g<lam j)).card) :
    (∀ j,lam j<γ-g ∨ γ+g<lam j) ∧
    (Finset.univ.filter (fun j => γ<lam j)).card=p := by
  classical
  let A := Finset.univ.filter (fun j : Fin d => γ-g≤lam j)
  let B := Finset.univ.filter (fun j : Fin d => γ+g<lam j)
  have hBA : B⊆A := by
    intro j hj
    simp only [B,Finset.mem_filter,Finset.mem_univ,true_and] at hj
    simp only [A,Finset.mem_filter,Finset.mem_univ,true_and]
    linarith
  have hc : A.card≤B.card := hlo.trans hhi
  have he : B=A := Finset.eq_of_subset_of_card_le hBA hc
  have ha : A.card=p := by
    dsimp [A,B] at he
    rw [he] at hhi
    exact le_antisymm hlo hhi
  have hd : ∀ j,lam j<γ-g ∨ γ+g<lam j := by
    intro j
    by_cases hj : lam j<γ-g
    · exact Or.inl hj
    · right
      have hjA : j∈A := Finset.mem_filter.mpr ⟨Finset.mem_univ _,le_of_not_gt hj⟩
      rw [←he] at hjA
      simpa only [B,Finset.mem_filter,Finset.mem_univ,true_and] using hjA
  refine ⟨hd,?_⟩
  have heC : Finset.univ.filter (fun j : Fin d => γ<lam j)=A := by
    ext j
    simp only [A,Finset.mem_filter,Finset.mem_univ,true_and]
    constructor
    · intro hj; linarith
    · intro hj
      rcases hd j with hh | hh
      · exact (not_lt_of_ge hj hh).elim
      · linarith
  rw [heC,ha]

end SmoothObstruction.RateThreshold

namespace SmoothObstruction.ShortBin
open scoped Matrix.Norms.L2Operator
variable {d L : ℕ} {K : ℝ}

/-- All witnesses in one bin share the same predetermined threshold and
rank. This proves the source bin threshold without singular-value minmax. -/
theorem common_gap {ι : Type*} (A : ι→Gauge d L K) (e : ι) {g δ : ℝ}
    (hg : 0<g) (hclose : ∀ i,‖(A i).product-(A e).product‖≤δ)
    (hdecay : Real.exp (-2*g*L+4*K)≤1/2)
    (hnoise : δ<Real.exp (-2*K)/2) :
    ∃ j : Fin (d+1), let γ := (1+8*(j.val:ℝ))*g
      ∀ i, (∀ k,(A i).lam k<γ-g ∨ γ+g<(A i).lam k) ∧
        (Finset.univ.filter (fun k => γ<(A i).lam k)).card=
          (Finset.univ.filter (fun k => γ<(A e).lam k)).card := by
  classical
  obtain ⟨j,hj⟩ := RateThreshold.exists_candidate d (A e).lam hg
  refine ⟨j,?_⟩
  dsimp only
  let γ := (1+8*(j.val:ℝ))*g
  have hγ : g≤γ := by
    dsimp [γ]
    nlinarith [Nat.cast_nonneg (α:=ℝ) j.val]
  have hrep : ∀ k,(A e).lam k<γ-3*g ∨ γ+3*g<(A e).lam k := by
    intro k
    have hh := hj k
    change 3*g < |(A e).lam k-γ| at hh
    rcases le_total ((A e).lam k) γ with hh' | hh'
    · rw [abs_of_nonpos (sub_nonpos.mpr hh')] at hh
      left; linarith
    · rw [abs_of_nonneg (sub_nonneg.mpr hh')] at hh
      right; linarith
  have hflo : Finset.univ.filter (fun k => γ-3*g<(A e).lam k)=
      Finset.univ.filter (fun k => γ<(A e).lam k) := by
    ext k
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    rcases hrep k with hh | hh <;> constructor <;> intro hh' <;> linarith
  have hfhi : Finset.univ.filter (fun k => γ+3*g≤(A e).lam k)=
      Finset.univ.filter (fun k => γ<(A e).lam k) := by
    ext k
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    rcases hrep k with hh | hh <;> constructor <;> intro hh' <;> linarith
  intro i
  have hlo := count_le (A i) (A e) (a:=γ-g) (b:=γ-3*g) (hclose i) (by
    convert exponential_separation (c:=γ-g) (l:=(L:ℝ)) (by linarith)
      (Nat.cast_nonneg L) hdecay hnoise using 1
    congr 2
    ring)
  have hclose' : ‖(A e).product-(A i).product‖≤δ := by
    rw [norm_sub_rev]; exact hclose i
  have hhi := count_le (A e) (A i) (a:=γ+3*g) (b:=γ+g) hclose' (by
    convert exponential_separation (c:=γ+3*g) (l:=(L:ℝ)) (by linarith)
      (Nat.cast_nonneg L) hdecay hnoise using 1
    congr 2
    ring)
  rw [hflo] at hlo
  rw [hfhi] at hhi
  exact RateThreshold.of_sandwich (A i).lam hg hlo hhi

end SmoothObstruction.ShortBin

namespace SmoothObstruction.ManifoldCoordinates
open Bundle Set Filter Topology
open scoped Manifold ContDiff Matrix.Norms.L2Operator
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- Exact identification of the diagonal-gauge propagator with the derivative
of the genuine nonautonomous chart expression. No product identity is assumed. -/
lemma actual_gauge_product (S : Diffeomorph I I M M ∞) (a : ℕ → M)
    (x : M) {N : ℕ} {K : ℝ} (A : ShortBin.Gauge d N K)
    (hchart : ∀ t≤N,S^[t] x∈(chartAt H (a t)).source)
    (hint : I.IsInteriorPoint x)
    (hEq : ∀ t<N,(Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm
      (coord I S (a t) (a (t+1)) (S^[t] x))*A.U t=
        A.U (t+1)*EuclideanSplitting.rate A.lam 1) :
    fderiv ℝ (ShortDerivative.iterate (fun t => localMap I S (a t) (a (t+1))) N)
      ((extChartAt I (a 0)) x)=A.product := by
  let F := Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)
  let D (t : ℕ) := coord I S (a t) (a (t+1)) (S^[t] x)
  let f (t : ℕ) := localMap I S (a t) (a (t+1))
  let X (t : ℕ) := (extChartAt I (a t)) (S^[t] x)
  have hi : ∀ t,I.IsInteriorPoint (S^[t] x) := by
    intro t
    induction t with
    | zero => exact hint
    | succ t ih =>
      rw [Function.iterate_succ_apply']
      exact ((S.isLocalDiffeomorph _).isInteriorPoint_iff (by simp)).mp ih
  have hx : ∀ t<N,f t (X t)=X (t+1) := by
    intro t ht
    simpa only [f,X,Function.iterate_succ_apply'] using
      localMap_coordinates I S (a t) (a (t+1)) (S^[t] x) (hchart t ht.le)
  have hd : ∀ t<N,HasFDerivAt (f t) (D t) (X t) := by
    intro t ht
    apply hasFDerivAt_localMap
    · refine ⟨hchart t ht.le,?_⟩
      simpa only [Set.mem_preimage,Function.iterate_succ_apply'] using hchart (t+1) (by omega)
    · exact (interior_coord I _ _ (hchart t ht.le)).mpr (hi t)
  have hder := (ShortDerivative.derivative_iterate f X D N hx hd).fderiv
  have hp : ∀ l,F (EuclideanSplitting.propagator (fun t => F.symm (D t)) 0 l)=
      RelativeProduct.segment D 0 l := by
    intro l
    induction l with
    | zero => simp only [EuclideanSplitting.propagator,RelativeProduct.segment_zero,map_one]
    | succ l ih =>
      simp only [EuclideanSplitting.propagator,RelativeProduct.segment_succ,Nat.zero_add,
        map_mul,StarAlgEquiv.apply_symm_apply,ih]
  have ht := EuclideanSplitting.propagator_eq_transition (fun t => F.symm (D t))
    A.U A.V A.lam A.UV A.VU N hEq 0 N (by omega)
  rw [←hp N,ht] at hder
  simpa only [f,X,Function.iterate_zero_apply,Nat.zero_add,ShortBin.Gauge.product,F] using hder
end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction.ManifoldCoordinates
open Bundle Set Filter Topology
open scoped Manifold ContDiff Matrix.Norms.L2Operator
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    {ι : Type*} [Fintype ι]

/-- A bin threshold for an arbitrary family of actual manifold witnesses,
including multiple gauges over one point. The constants are chosen uniformly
from the finite compact atlas, before any bin, witness or frame is chosen.
Short derivative closeness and chart carrying are proved, not assumed.
Only the available finite gauge equations and the explicit scale inequalities
remain as inputs. -/
theorem uniform_actual_bin_threshold (hclosed : IsClosed (range I))
    (S : Diffeomorph I I M M ∞) (a : ι → M) (K : ι → Set M)
    (hK : ∀ i,IsCompact (K i)) (hKU : ∀ i,K i⊆(chartAt H (a i)).source) :
    ∃ r C : ℝ,0<r ∧ 1≤C ∧
      ∀ (J : Type*) (x : J → M) (e : J) (c : ℕ → ι) (N : ℕ) (B g h : ℝ)
        (A : J → ShortBin.Gauge d N B),
        (∀ t≤N,S^[t] (x e)∈K (c t)) →
        (∀ i,I.IsInteriorPoint (x i)) →
        (∀ i,x i∈(chartAt H (a (c 0))).source) →
        (∀ i,‖(extChartAt I (a (c 0))) (x i)-(extChartAt I (a (c 0))) (x e)‖≤h) →
        C ^ N*h≤r →
        (∀ i,∀ t<N,(Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm
          (coord I S (a (c t)) (a (c (t+1))) (S^[t] (x i)))*(A i).U t=
            (A i).U (t+1)*EuclideanSplitting.rate (A i).lam 1) →
        0<g → Real.exp (-2*g*N+4*B)≤1/2 →
        N*C*C ^ (2*N)*h<Real.exp (-2*B)/2 →
        ∃ j : Fin (d+1), let γ := (1+8*(j.val:ℝ))*g
          ∀ i,(∀ k,(A i).lam k<γ-g ∨ γ+g<(A i).lam k) ∧
            (Finset.univ.filter (fun k => γ<(A i).lam k)).card=
              (Finset.univ.filter (fun k => γ<(A e).lam k)).card := by
  classical
  obtain ⟨r,C,hr,hC,hh⟩ := actual_short_comparison I hclosed S a K hK hKU
  refine ⟨r,C,hr,hC,fun J x e c N B g h A hxs hint hsource hdist hsmall hEq hg hdecay hnoise => ?_⟩
  have hC0 : 0≤C := le_trans (by norm_num) hC
  have hs (i : J) := hh c (x e) (x i) N hxs (hint e) (hint i) (hsource i)
    ((mul_le_mul_of_nonneg_left (hdist i) (pow_nonneg hC0 N)).trans hsmall)
  have hprod (i : J) := actual_gauge_product I S (fun t => a (c t)) (x i) (A i)
    (fun t ht => (hs i).1 t ht |>.1) (hint i) (hEq i)
  apply ShortBin.common_gap A e hg (δ:=N*C*C ^ (2*N)*h) ?_ hdecay hnoise
  intro i
  rw [←hprod i,←hprod e]
  exact ((hs i).2).trans (mul_le_mul_of_nonneg_left (hdist i) (by positivity))
end SmoothObstruction.ManifoldCoordinates

namespace SmoothObstruction.DirectedProjection
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

noncomputable def restrictProjection (U V : Submodule ℝ E) : U →L[ℝ] V :=
  V.orthogonalProjectionOnto.comp U.subtypeL

lemma lower (U V : Submodule ℝ E) {ε : ℝ} (hε : ε ≤ 1/2)
    (h : ∀ x : U, ‖(x:E)-V.starProjection x‖ ≤ ε*‖x‖) (x : U) :
    ‖x‖ ≤ 2*‖restrictProjection U V x‖ := by
  have hh : ‖x‖ ≤ ‖(x:E)-V.starProjection x‖+‖V.starProjection x‖ := by
    calc
      _ = ‖((x:E)-V.starProjection x)+V.starProjection x‖ := by rw [sub_add_cancel]; rfl
      _ ≤ _ := norm_add_le _ _
  have he := (h x).trans (mul_le_mul_of_nonneg_right hε (norm_nonneg _))
  change ‖x‖ ≤ 2*‖V.starProjection x‖
  linarith

noncomputable def equiv (U V : Submodule ℝ E)
    (hdim : Module.finrank ℝ U=Module.finrank ℝ V) {ε : ℝ} (hε : ε ≤ 1/2)
    (h : ∀ x : U, ‖(x:E)-V.starProjection x‖ ≤ ε*‖x‖) : U ≃L[ℝ] V :=
  (LinearMap.linearEquivOfInjective (restrictProjection U V).toLinearMap (by
    intro x y hxy
    change restrictProjection U V x=restrictProjection U V y at hxy
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    have hh := lower U V hε h (x-y)
    rw [map_sub,hxy,sub_self,norm_zero,mul_zero] at hh
    exact le_antisymm hh (norm_nonneg _)) hdim).toContinuousLinearEquiv

@[simp] lemma equiv_apply (U V : Submodule ℝ E)
    (hdim : Module.finrank ℝ U=Module.finrank ℝ V) {ε : ℝ} (hε : ε ≤ 1/2)
    (h : ∀ x : U, ‖(x:E)-V.starProjection x‖ ≤ ε*‖x‖) (x : U) :
    equiv U V hdim hε h x=restrictProjection U V x := rfl

lemma reverse_directed (U V : Submodule ℝ E)
    (hdim : Module.finrank ℝ U=Module.finrank ℝ V) {ε : ℝ} (hε0 : 0≤ε) (hε : ε ≤ 1/2)
    (h : ∀ x : U, ‖(x:E)-V.starProjection x‖ ≤ ε*‖x‖) (y : V) :
    ‖(y:E)-U.starProjection y‖ ≤ 2*ε*‖y‖ := by
  let e := equiv U V hdim hε h
  let x := e.symm y
  have hxy : V.starProjection x=(y:E) := by
    have hh := congrArg (fun v : V => (v:E)) (e.apply_symm_apply y)
    exact hh
  have hn : ‖x‖ ≤ 2*‖y‖ := by
    have hh := lower U V hε h x
    change ‖x‖ ≤ 2*‖V.starProjection x‖ at hh
    rwa [hxy] at hh
  calc
    ‖(y:E)-U.starProjection y‖ ≤ ‖(y:E)-x‖ := by
      rw [Submodule.starProjection_minimal]
      exact ciInf_le ⟨0, Set.forall_mem_range.mpr fun _ => norm_nonneg _⟩ x
    _ = ‖(x:E)-V.starProjection x‖ := by rw [hxy,norm_sub_rev]
    _ ≤ ε*‖x‖ := h x
    _ ≤ ε*(2*‖y‖) := mul_le_mul_of_nonneg_left hn hε0
    _ = _ := by ring

lemma one_sided_norm (U V : Submodule ℝ E) {ε : ℝ} (hε : 0≤ε)
    (h : ∀ x : U, ‖(x:E)-V.starProjection x‖ ≤ ε*‖x‖) :
    ‖(1-V.starProjection)*U.starProjection‖ ≤ ε := by
  apply ContinuousLinearMap.opNorm_le_bound _ hε
  intro x
  change ‖U.starProjection x-V.starProjection (U.starProjection x)‖ ≤ ε*‖x‖
  exact (h (U.orthogonalProjectionOnto x)).trans
    (mul_le_mul_of_nonneg_left (U.norm_starProjection_apply_le x) hε)

/-- A directed subspace estimate and equality of dimensions imply a full
projector-distance bound. No chosen singular-vector continuity is assumed. -/
theorem projector_distance (U V : Submodule ℝ E)
    (hdim : Module.finrank ℝ U=Module.finrank ℝ V) {ε : ℝ} (hε0 : 0≤ε) (hε : ε ≤ 1/2)
    (h : ∀ x : U, ‖(x:E)-V.starProjection x‖ ≤ ε*‖x‖) :
    ‖U.starProjection-V.starProjection‖ ≤ 3*ε := by
  have hA := one_sided_norm U V hε0 h
  have hB := one_sided_norm V U (by positivity : 0≤2*ε)
    (reverse_directed U V hdim hε0 hε h)
  have he : U.starProjection-V.starProjection =
      (1-V.starProjection)*U.starProjection-star ((1-U.starProjection)*V.starProjection) := by
    rw [star_mul,star_sub,star_one,(isSelfAdjoint_starProjection U).star_eq,
      (isSelfAdjoint_starProjection V).star_eq]
    noncomm_ring
  rw [he]
  calc
    _ ≤ ‖(1-V.starProjection)*U.starProjection‖+
        ‖star ((1-U.starProjection)*V.starProjection)‖ := norm_sub_le _ _
    _ = ‖(1-V.starProjection)*U.starProjection‖+
        ‖(1-U.starProjection)*V.starProjection‖ := by
      congr 1
      exact ContinuousLinearMap.adjoint.norm_map _
    _ ≤ ε+2*ε := add_le_add hA hB
    _ = _ := by ring

end SmoothObstruction.DirectedProjection

namespace SmoothObstruction.ShortBin
open EuclideanSplitting
open scoped Matrix.Norms.L2Operator
variable {d L : ℕ} {K : ℝ}

lemma Gauge.complement_mem (A : Gauge d L K) (S : Finset (Fin d))
    (x : EuclideanSpace ℝ (Fin d)) :
    x-Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (projection A.U A.V Sᶜ 0) x∈A.space S := by
  have he := congrArg (fun M : Matrix (Fin d) (Fin d) ℝ =>
    Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) M x) (projection_compl A.U A.V A.UV S 0)
  rw [map_add,_root_.add_apply,map_one] at he
  change Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (projection A.U A.V S 0) x+
    Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (projection A.U A.V Sᶜ 0) x=x at he
  rw [←eq_sub_iff_add_eq.mpr he]
  apply (groupSpace_fixed _ _ _ _ _ _).mpr
  change Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (projection A.U A.V S 0)
    (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (projection A.U A.V S 0) x)=_
  rw [←mul_apply_eq_comp,←map_mul,projection_idem A.U A.V A.VU]

/-- Actual short-product control of the slow subspace. The inverse fast
propagator is constructed, rather than supplied as a desired estimate. -/
lemma slow_directed (A B : Gauge d L K) (S T : Finset (Fin d)) {γ g δ : ℝ}
    (hclose : ‖A.product-B.product‖≤δ)
    (hAf : ∀ j∈Sᶜ,γ+g≤A.lam j) (hBs : ∀ j∈T,B.lam j≤γ-g) :
    ∀ x : B.space T, ‖(x:EuclideanSpace ℝ (Fin d))-(A.space S).starProjection x‖ ≤
      Real.exp (-(γ+g)*L+2*K)*(Real.exp ((γ-g)*L+2*K)+δ)*‖x‖ := by
  let J := Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)
    (transition A.U A.V A.lam L 0*projection A.U A.V Sᶜ L)
  let P := Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (projection A.U A.V Sᶜ 0)
  have hJP : J.comp A.product=P := by
    change Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)
      (transition A.U A.V A.lam L 0*projection A.U A.V Sᶜ L)*
      Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (transition A.U A.V A.lam 0 L)=_
    rw [←map_mul,inverse_fast_product A.U A.V A.UV A.VU]
  have hJ : ‖J‖≤Real.exp (-(γ+g)*L+2*K) := by
    dsimp only [J]
    rw [Matrix.l2_opNorm_toEuclideanCLM]
    simpa only [Nat.cast_zero,sub_zero] using
      norm_backward_projection A.U A.V A.VU A.lam Sᶜ 0 L (Nat.zero_le L)
        (A.normU 0 (Nat.zero_le L)) (A.normV L le_rfl) hAf
  exact SubspaceComparison.directed_of_product A.product B.product J P (B.space T) (A.space S)
    (Real.exp_nonneg _) hJP hJ hclose (B.upper T hBs) (A.complement_mem S)

lemma slow_projector_distance (A B : Gauge d L K) (S T : Finset (Fin d))
    {γ g δ : ℝ} (hdim : S.card=T.card)
    (hclose : ‖A.product-B.product‖≤δ)
    (hAf : ∀ j∈Sᶜ,γ+g≤A.lam j) (hBs : ∀ j∈T,B.lam j≤γ-g)
    (hδ : 0≤δ)
    (hsmall : Real.exp (-(γ+g)*L+2*K)*(Real.exp ((γ-g)*L+2*K)+δ)≤1/2) :
    ‖(B.space T).starProjection-(A.space S).starProjection‖ ≤
      3*(Real.exp (-(γ+g)*L+2*K)*(Real.exp ((γ-g)*L+2*K)+δ)) := by
  apply DirectedProjection.projector_distance _ _
    (by rw [A.rank,B.rank,hdim]) (by positivity) hsmall
  exact slow_directed A B S T hclose hAf hBs

end SmoothObstruction.ShortBin

namespace SmoothObstruction.ShortBin
open EuclideanSplitting
open scoped Matrix.Norms.L2Operator
variable {d L : ℕ} {K : ℝ}

/-- A simultaneous fixed threshold and two common reference subspaces for
all two-sided finite gauges in a bin. The two backward gauges are compared
through their actual products, not through continuity of frame choices. -/
theorem common_splittings {ι : Type*} (A Z : ι → Gauge d L K) (e : ι)
    {g δ : ℝ} (hg : 0<g) (hδ : 0≤δ)
    (hforward : ∀ i,‖(A i).product-(A e).product‖≤δ)
    (hbackward : ∀ i,‖(Z i).product-(Z e).product‖≤δ)
    (hU : ∀ i,(Z i).U 0=(A i).U 0) (hV : ∀ i,(Z i).V 0=(A i).V 0)
    (hlam : ∀ i k,(Z i).lam k= -(A i).lam k)
    (hdecay : Real.exp (-2*g*L+4*K)≤1/2)
    (hnoise : δ<Real.exp (-2*K)/2)
    (hsmall : Real.exp (-2*g*L+4*K)+δ*Real.exp ((1+8*(d:ℝ))*g*L+2*K)≤1/2) :
    ∃ j : Fin (d+1), let γ := (1+8*(j.val:ℝ))*g
      (∀ i,(∀ k,(A i).lam k<γ-g ∨ γ+g<(A i).lam k) ∧
        (Finset.univ.filter (fun k => γ<(A i).lam k)).card=
          (Finset.univ.filter (fun k => γ<(A e).lam k)).card) ∧
      let ε := Real.exp (-2*g*L+4*K)+δ*Real.exp ((1+8*(d:ℝ))*g*L+2*K)
      (∀ i,‖((A i).space (Finset.univ.filter (fun k => (A i).lam k≤γ))).starProjection-
        ((A e).space (Finset.univ.filter (fun k => (A e).lam k≤γ))).starProjection‖≤3*ε) ∧
      ∀ i,‖((A i).space (Finset.univ.filter (fun k => γ<(A i).lam k))).starProjection-
        ((A e).space (Finset.univ.filter (fun k => γ<(A e).lam k))).starProjection‖≤3*ε := by
  classical
  obtain ⟨j,hj⟩ := common_gap A e hg hforward hdecay hnoise
  refine ⟨j,hj,?_⟩
  let γ := (1+8*(j.val:ℝ))*g
  let Γ := (1+8*(d:ℝ))*g
  let ε := Real.exp (-2*g*L+4*K)+δ*Real.exp (Γ*L+2*K)
  let slow (i : ι) := Finset.univ.filter (fun k => (A i).lam k≤γ)
  let fast (i : ι) := Finset.univ.filter (fun k => γ<(A i).lam k)
  have hγ : g≤γ ∧ γ≤Γ := by
    have hval : (j.val:ℝ)≤d := by exact_mod_cast (show j.val≤d by omega)
    dsimp [γ,Γ]
    constructor <;> nlinarith [Nat.cast_nonneg (α:=ℝ) j.val]
  have hf (i : ι) (k : Fin d) (hk : k∈fast i) : γ+g≤(A i).lam k := by
    have hh : γ<(A i).lam k := by simpa only [fast,Finset.mem_filter,Finset.mem_univ,true_and] using hk
    rcases (hj i).1 k with h | h <;> linarith
  have hs (i : ι) (k : Fin d) (hk : k∈slow i) : (A i).lam k≤γ-g := by
    have hh : (A i).lam k≤γ := by simpa only [slow,Finset.mem_filter,Finset.mem_univ,true_and] using hk
    rcases (hj i).1 k with h | h <;> linarith
  have hsc (i : ι) : (slow i)ᶜ=fast i := by ext k; simp [slow,fast]
  have hfc (i : ι) : (fast i)ᶜ=slow i := by ext k; simp [slow,fast]
  have hfdim (i : ι) : (fast e).card=(fast i).card := (hj i).2.symm
  have hsdim (i : ι) : (slow e).card=(slow i).card := by
    rw [←hfc e,←hfc i,Finset.card_compl,Finset.card_compl,hfdim i]
  have hbound (a : ℝ) (ha : a≤Γ) :
      Real.exp (a*L+2*K)*(Real.exp ((-2*g-a)*L+2*K)+δ)≤ε := by
    rw [mul_add,←Real.exp_add]
    have hE : a*(L:ℝ)+2*K+((-2*g-a)*L+2*K)= -2*g*L+4*K := by ring
    rw [hE]
    change Real.exp (-2*g*L+4*K)+Real.exp (a*L+2*K)*δ ≤
      Real.exp (-2*g*L+4*K)+δ*Real.exp (Γ*L+2*K)
    apply add_le_add (le_refl _)
    rw [mul_comm]
    apply mul_le_mul_of_nonneg_left _ hδ
    apply Real.exp_le_exp.mpr
    exact add_le_add (mul_le_mul_of_nonneg_right ha (Nat.cast_nonneg L)) (le_refl _)
  have hp : Real.exp (-(γ+g)*L+2*K)*(Real.exp ((γ-g)*L+2*K)+δ)≤ε := by
    have heq : -2*g- (-(γ+g))=γ-g := by ring
    simpa only [heq] using hbound (-(γ+g)) (by linarith)
  have hm : Real.exp ((γ-g)*L+2*K)*(Real.exp ((-γ-g)*L+2*K)+δ)≤ε := by
    have heq : -2*g-(γ-g)= -γ-g := by ring
    simpa only [heq] using hbound (γ-g) (by linarith)
  have hZ (i : ι) (S : Finset (Fin d)) : (Z i).space S=(A i).space S := by
    simp only [Gauge.space,hU,hV]
  constructor
  · intro i
    apply (slow_projector_distance (A e) (A i) (slow e) (slow i) (hsdim i)
      (by rw [norm_sub_rev]; exact hforward i)
      (by rw [hsc]; exact hf e) (hs i) hδ (hp.trans hsmall)).trans
    exact mul_le_mul_of_nonneg_left hp (by norm_num)
  · intro i
    have hneg : -(-γ+g)=γ-g := by ring
    have ht := slow_projector_distance (Z e) (Z i) (fast e) (fast i)
      (γ:=-γ) (g:=g) (δ:=δ) (hfdim i)
      (by rw [norm_sub_rev]; exact hbackward i)
      (by intro k hk; rw [hlam]; have hh := hs e k (hfc e ▸ hk); linarith)
      (by intro k hk; rw [hlam]; have hh := hf i k hk; linarith) hδ
      (by simpa only [hneg] using hm.trans hsmall)
    rw [hZ i,hZ e,hneg] at ht
    exact ht.trans (mul_le_mul_of_nonneg_left hm (by norm_num))
end SmoothObstruction.ShortBin

namespace SmoothObstruction.ManifoldCoordinates
open Bundle Set Filter Topology
open scoped Manifold ContDiff Matrix.Norms.L2Operator
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    {ι : Type*} [Fintype ι]

/-- Uniform common reference spaces for actual two-sided smooth orbit
witnesses in one bin. Neither continuity of frame choices nor short-product
closeness is assumed: both comparisons are taken along the genuine forward
and backward orbits, with chart carrying proved from initial closeness. -/
theorem uniform_actual_bin_splitting (hclosed : IsClosed (range I))
    (S : Diffeomorph I I M M ∞) (a : ι → M) (K : ι → Set M)
    (hK : ∀ i,IsCompact (K i)) (hKU : ∀ i,K i⊆(chartAt H (a i)).source) :
    ∃ rF CF rB CB : ℝ,0<rF ∧ 1≤CF ∧ 0<rB ∧ 1≤CB ∧
      ∀ (J : Type*) (x : J → M) (e : J) (cF cB : ℕ → ι) (N : ℕ) (B g h : ℝ)
        (A Z : J → ShortBin.Gauge d N B),
        cB 0=cF 0 →
        (∀ t≤N,S^[t] (x e)∈K (cF t)) →
        (∀ t≤N,S.symm^[t] (x e)∈K (cB t)) →
        (∀ i,I.IsInteriorPoint (x i)) →
        (∀ i,x i∈(chartAt H (a (cF 0))).source) →
        (∀ i,‖(extChartAt I (a (cF 0))) (x i)-(extChartAt I (a (cF 0))) (x e)‖≤h) →
        CF ^ N*h≤rF → CB ^ N*h≤rB →
        (∀ i,∀ t<N,(Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm
          (coord I S (a (cF t)) (a (cF (t+1))) (S^[t] (x i)))*(A i).U t=
            (A i).U (t+1)*EuclideanSplitting.rate (A i).lam 1) →
        (∀ i,∀ t<N,(Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm
          (coord I S.symm (a (cB t)) (a (cB (t+1))) (S.symm^[t] (x i)))*(Z i).U t=
            (Z i).U (t+1)*EuclideanSplitting.rate (Z i).lam 1) →
        (∀ i,(Z i).U 0=(A i).U 0) → (∀ i,(Z i).V 0=(A i).V 0) →
        (∀ i k,(Z i).lam k= -(A i).lam k) →
        0<g → Real.exp (-2*g*N+4*B)≤1/2 →
        let δ := ((N:ℝ)*CF*CF ^ (2*N)+N*CB*CB ^ (2*N))*h
        δ<Real.exp (-2*B)/2 →
        Real.exp (-2*g*N+4*B)+δ*Real.exp ((1+8*(d:ℝ))*g*N+2*B)≤1/2 →
        ∃ j : Fin (d+1), let γ := (1+8*(j.val:ℝ))*g
          (∀ i,(∀ k,(A i).lam k<γ-g ∨ γ+g<(A i).lam k) ∧
            (Finset.univ.filter (fun k => γ<(A i).lam k)).card=
              (Finset.univ.filter (fun k => γ<(A e).lam k)).card) ∧
          let ε := Real.exp (-2*g*N+4*B)+δ*Real.exp ((1+8*(d:ℝ))*g*N+2*B)
          (∀ i,‖((A i).space (Finset.univ.filter (fun k => (A i).lam k≤γ))).starProjection-
            ((A e).space (Finset.univ.filter (fun k => (A e).lam k≤γ))).starProjection‖≤3*ε) ∧
          ∀ i,‖((A i).space (Finset.univ.filter (fun k => γ<(A i).lam k))).starProjection-
            ((A e).space (Finset.univ.filter (fun k => γ<(A e).lam k))).starProjection‖≤3*ε := by
  classical
  obtain ⟨rF,CF,hrF,hCF,hhF⟩ := actual_short_comparison I hclosed S a K hK hKU
  obtain ⟨rB,CB,hrB,hCB,hhB⟩ := actual_short_comparison I hclosed S.symm a K hK hKU
  refine ⟨rF,CF,rB,CB,hrF,hCF,hrB,hCB,
    fun J x e cF cB N B g h A Z h0 hxsF hxsB hint hsource hdist hsF hsB hEqF hEqB hU hV hlam hg hdecay hnoise hsmall => ?_⟩
  have hCF0 : 0≤CF := le_trans (by norm_num) hCF
  have hCB0 : 0≤CB := le_trans (by norm_num) hCB
  have hh0 : 0≤h := (norm_nonneg _).trans (hdist e)
  have hdistB (i : J) : ‖(extChartAt I (a (cB 0))) (x i)-(extChartAt I (a (cB 0))) (x e)‖≤h := by
    simpa only [h0] using hdist i
  have hsourceB (i : J) : x i∈(chartAt H (a (cB 0))).source := by
    simpa only [h0] using hsource i
  have hcF (i : J) := hhF cF (x e) (x i) N hxsF (hint e) (hint i) (hsource i)
    ((mul_le_mul_of_nonneg_left (hdist i) (pow_nonneg hCF0 N)).trans hsF)
  have hcB (i : J) := hhB cB (x e) (x i) N hxsB (hint e) (hint i) (hsourceB i)
    ((mul_le_mul_of_nonneg_left (hdistB i) (pow_nonneg hCB0 N)).trans hsB)
  have hpF (i : J) := actual_gauge_product I S (fun t => a (cF t)) (x i) (A i)
    (fun t ht => (hcF i).1 t ht |>.1) (hint i) (hEqF i)
  have hpB (i : J) := actual_gauge_product I S.symm (fun t => a (cB t)) (x i) (Z i)
    (fun t ht => (hcB i).1 t ht |>.1) (hint i) (hEqB i)
  apply ShortBin.common_splittings A Z e hg (by positivity) _ _ hU hV hlam hdecay hnoise hsmall
  · intro i
    rw [←hpF i,←hpF e]
    apply ((hcF i).2).trans
    apply (mul_le_mul_of_nonneg_left (hdist i) (by positivity)).trans
    apply mul_le_mul_of_nonneg_right _ hh0
    exact le_add_of_nonneg_right (by positivity)
  · intro i
    rw [←hpB i,←hpB e]
    apply ((hcB i).2).trans
    apply (mul_le_mul_of_nonneg_left (hdistB i) (by positivity)).trans
    apply mul_le_mul_of_nonneg_right _ hh0
    exact le_add_of_nonneg_left (by positivity)
end SmoothObstruction.ManifoldCoordinates

end

end OAI
