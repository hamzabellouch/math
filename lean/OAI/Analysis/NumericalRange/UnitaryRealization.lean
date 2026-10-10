import OAI.Analysis.NumericalRange.PulledDensity

namespace OAI

noncomputable section

namespace CompleteCrouzeix


universe u_157 u_158 u_159 u_160 u_161 u_162 u_163 u_164 u_165 u_166 u_167 u_168 u_169 u_170 u_171 u_172 u_173 u_174 u_175 u_176

open scoped BigOperators Matrix.Norms.L2Operator
open Polynomial Finset


open Filter Topology
open scoped ENNReal Matrix ComplexOrder Matrix.Norms.L2Operator MatrixOrder
section


open MeasureTheory
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
variable {n : Type u_162} [Fintype n] [DecidableEq n]

open scoped Kronecker

variable {m : Type u_163} [Fintype m] [DecidableEq m]


open Filter Topology MeasureTheory Set Metric
open scoped ENNReal NNReal Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
variable {n : Type u_164} [Fintype n] [DecidableEq n]


open Filter Topology MeasureTheory Set Metric
open scoped ENNReal NNReal Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
variable {n : Type u_165} [Fintype n] [DecidableEq n]


open Filter Topology MeasureTheory Set Metric
open scoped ENNReal NNReal Matrix.Norms.L2Operator MatrixOrder Kronecker
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
variable {n : Type u_166} {m : Type u_167} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

end


section
open scoped InnerProductSpace
variable {E : Type u_173} {V : Type u_174} [NormedAddCommGroup E] [NormedAddCommGroup V]
  [InnerProductSpace ℂ E] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

theorem exists_unitary_intertwining (f g : E →ₗ[ℂ] V)
    (hn : ∀ x, ‖f x‖ = ‖g x‖) :
    ∃ U : V ≃ₗᵢ[ℂ] V, ∀ x, U (f x) = g x := by
  have hk : LinearMap.ker f ≤ LinearMap.ker g := by
    intro x hx
    change g x = 0
    apply norm_eq_zero.mp
    rw [← hn, LinearMap.mem_ker.mp hx, norm_zero]
  let L : LinearMap.range f →ₗ[ℂ] V :=
    ((LinearMap.ker f).liftQ g hk).comp f.quotKerEquivRange.symm.toLinearMap
  have hL (x : E) (hx : f x ∈ LinearMap.range f) : L ⟨f x,hx⟩ = g x := by
    simp only [L,LinearMap.comp_apply,LinearEquiv.coe_coe,
      LinearMap.quotKerEquivRange_symm_apply_image]
    exact Submodule.liftQ_apply _ _ x
  have hnL : ∀ v : LinearMap.range f, ‖L v‖ = ‖v‖ := by
    intro v
    obtain ⟨x,hx⟩ := v.property
    have he : v = ⟨f x,LinearMap.mem_range_self f x⟩ := Subtype.ext hx.symm
    rw [he,hL]
    exact (hn x).symm
  let I : LinearMap.range f →ₗᵢ[ℂ] V := { toLinearMap := L, norm_map' := hnL }
  let U : V →ₗᵢ[ℂ] V := I.extend
  have hs : Function.Surjective U :=
    LinearMap.surjective_of_injective (f := U.toLinearMap) U.injective
  refine ⟨LinearIsometryEquiv.ofSurjective U hs,?_⟩
  intro x
  change I.extend (f x) = g x
  rw [← show (⟨f x,LinearMap.mem_range_self f x⟩ : LinearMap.range f).val = f x from rfl,
    I.extend_apply]
  exact hL x _

variable [CompleteSpace E] [CompleteSpace V]

theorem exists_unitary_of_row_gram (R₁ R₂ : V →L[ℂ] E)
    (h : R₁.comp R₁.adjoint = R₂.comp R₂.adjoint) :
    ∃ U : V ≃ₗᵢ[ℂ] V, ∀ x, U (R₂.adjoint x) = R₁.adjoint x := by
  refine exists_unitary_intertwining R₂.adjoint.toLinearMap R₁.adjoint.toLinearMap ?_
  intro x
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have hh : inner ℂ (R₂.adjoint x) (R₂.adjoint x) =
      inner ℂ (R₁.adjoint x) (R₁.adjoint x) := by
    rw [ContinuousLinearMap.adjoint_inner_left,ContinuousLinearMap.adjoint_inner_left]
    exact congrArg (fun L : E →L[ℂ] E => inner ℂ x (L x)) h.symm
  rw [norm_sq_eq_re_inner (𝕜 := ℂ),norm_sq_eq_re_inner (𝕜 := ℂ)]
  exact congrArg (RCLike.re (K := ℂ)) hh

end

open scoped Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder
section
variable {n : Type u_175} [Fintype n] [DecidableEq n]

theorem exists_unitary_matrix_of_gram (R₁ R₂ : Matrix n n ℂ)
    (h : R₁*R₁ᴴ = R₂*R₂ᴴ) :
    ∃ U : Matrix n n ℂ, Uᴴ*U = 1 ∧ U*Uᴴ = 1 ∧ R₁ = R₂*U := by
  let e := Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)
  have he_mul (A B : Matrix n n ℂ) : e (A*B) = e A * e B := e.map_mul A B
  have he_star (A : Matrix n n ℂ) : e Aᴴ = (e A).adjoint := map_star e A
  have he_one : e (1 : Matrix n n ℂ) = 1 := map_one e
  have hh : (e R₁).comp (e R₁).adjoint = (e R₂).comp (e R₂).adjoint := by
    have := congrArg e h
    simpa only [he_mul,he_star,ContinuousLinearMap.mul_def] using this
  obtain ⟨u,hu⟩ := exists_unitary_of_row_gram (e R₁) (e R₂) hh
  let U := e.symm (u.symm : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
  have hU : e U = (u.symm : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) := e.apply_symm_apply _
  refine ⟨U,?_,?_,?_⟩
  · apply e.injective
    change e (Uᴴ*U) = e 1
    rw [he_mul,he_star,he_one,hU,LinearIsometryEquiv.adjoint_eq_symm]
    ext x
    simp
  · apply e.injective
    change e (U*Uᴴ) = e 1
    rw [he_mul,he_star,he_one,hU,LinearIsometryEquiv.adjoint_eq_symm]
    ext x
    simp
  · apply e.injective
    have hr : (u : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) * (e R₂).adjoint =
        (e R₁).adjoint := by apply ContinuousLinearMap.ext; intro x; exact hu x
    have hs := congrArg star hr
    simp only [star_mul, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_adjoint,
      LinearIsometryEquiv.adjoint_eq_symm] at hs
    change e R₁ = e (R₂*U)
    rw [he_mul,hU]
    exact hs.symm

theorem exists_unitary_row_realization (D X Y L : Matrix n n ℂ)
    (hb : X*Xᴴ-Y*Yᴴ = L*Lᴴ-D*(L*Lᴴ)*Dᴴ) :
    ∃ a b c d : Matrix n n ℂ,
      let U := Matrix.fromBlocks a b c d
      Uᴴ*U = 1 ∧ U*Uᴴ = 1 ∧ L = D*L*a+X*c ∧ Y = D*L*b+X*d := by
  let R₁ : Matrix (n ⊕ n) (n ⊕ n) ℂ := Matrix.fromBlocks L Y 0 0
  let R₂ : Matrix (n ⊕ n) (n ⊕ n) ℂ := Matrix.fromBlocks (D*L) X 0 0
  have hr : R₁*R₁ᴴ = R₂*R₂ᴴ := by
    simp only [R₁,R₂,Matrix.fromBlocks_conjTranspose,Matrix.conjTranspose_zero,
      Matrix.fromBlocks_multiply,Matrix.mul_zero,Matrix.zero_mul,add_zero]
    congr 1
    rw [Matrix.conjTranspose_mul]
    have he : D*L*(Lᴴ*Dᴴ) = D*(L*Lᴴ)*Dᴴ := by noncomm_ring
    rw [he]
    linear_combination (norm := abel) -hb
  obtain ⟨U,hu,hu',hrU⟩ := exists_unitary_matrix_of_gram R₁ R₂ hr
  refine ⟨U.toBlocks₁₁,U.toBlocks₁₂,U.toBlocks₂₁,U.toBlocks₂₂,?_⟩
  dsimp only
  rw [Matrix.fromBlocks_toBlocks]
  refine ⟨hu,hu',?_,?_⟩
  · have hh := congrArg Matrix.toBlocks₁₁ hrU
    rw [← Matrix.fromBlocks_toBlocks U] at hh
    simpa only [R₁,R₂,Matrix.fromBlocks_multiply,Matrix.toBlocks_fromBlocks₁₁] using hh
  · have hh := congrArg Matrix.toBlocks₁₂ hrU
    rw [← Matrix.fromBlocks_toBlocks U] at hh
    simpa only [R₁,R₂,Matrix.fromBlocks_multiply,Matrix.toBlocks_fromBlocks₁₂] using hh

lemma block_one₁₁
    {n : Type u_175} [Fintype n] [DecidableEq n] :
    (1 : Matrix (n ⊕ n) (n ⊕ n) ℂ).toBlocks₁₁ = (1 : Matrix n n ℂ) := by
  ext i j
  simp [Matrix.toBlocks₁₁,Matrix.one_apply]

lemma block_one₂₂
    {n : Type u_175} [Fintype n] [DecidableEq n] :
    (1 : Matrix (n ⊕ n) (n ⊕ n) ℂ).toBlocks₂₂ = (1 : Matrix n n ℂ) := by
  ext i j
  simp [Matrix.toBlocks₂₂,Matrix.one_apply]

lemma norm_le_one_of_star_mul_le {A : Matrix n n ℂ} (h : Aᴴ*A ≤ 1) : ‖A‖ ≤ 1 := by
  have hn := (CStarAlgebra.norm_le_one_iff_of_nonneg _
    (Matrix.posSemidef_conjTranspose_mul_self A).nonneg).mpr h
  rw [Matrix.l2_opNorm_conjTranspose_mul_self] at hn
  nlinarith [norm_nonneg A]

lemma block_unitary_contractions {a b c d : Matrix n n ℂ}
    (hU : (Matrix.fromBlocks a b c d)ᴴ * Matrix.fromBlocks a b c d = 1) :
    ‖a‖ ≤ 1 ∧ ‖b‖ ≤ 1 ∧ ‖c‖ ≤ 1 ∧ ‖d‖ ≤ 1 := by
  have h₁ := congrArg Matrix.toBlocks₁₁ hU
  have h₂ := congrArg Matrix.toBlocks₂₂ hU
  simp only [Matrix.fromBlocks_conjTranspose,Matrix.fromBlocks_multiply,
    Matrix.toBlocks_fromBlocks₁₁,block_one₁₁] at h₁
  simp only [Matrix.fromBlocks_conjTranspose,Matrix.fromBlocks_multiply,
    Matrix.toBlocks_fromBlocks₂₂,block_one₂₂] at h₂
  have hpos (A : Matrix n n ℂ) : 0 ≤ Aᴴ*A :=
    (Matrix.posSemidef_conjTranspose_mul_self A).nonneg
  refine ⟨norm_le_one_of_star_mul_le ?_,norm_le_one_of_star_mul_le ?_,
    norm_le_one_of_star_mul_le ?_,norm_le_one_of_star_mul_le ?_⟩
  · rw [← h₁]; exact le_add_of_nonneg_right (hpos c)
  · rw [← h₂]; exact le_add_of_nonneg_right (hpos d)
  · rw [← h₁]; exact le_add_of_nonneg_left (hpos a)
  · rw [← h₂]; exact le_add_of_nonneg_left (hpos b)

def transfer (a b c d : Matrix n n ℂ) (z : ℂ) : Matrix n n ℂ :=
  d + z • (c * (1-z • a)⁻¹ * b)

theorem transfer_contraction {a b c d : Matrix n n ℂ}
    (hU : (Matrix.fromBlocks a b c d)ᴴ * Matrix.fromBlocks a b c d = 1)
    {z : ℂ} (hz : ‖z‖ < 1) : ‖transfer a b c d z‖ ≤ 1 := by
  have ha := (block_unitary_contractions hU).1
  have hza : ‖z • a‖ < 1 := by
    rw [norm_smul]
    exact (mul_le_mul_of_nonneg_left ha (norm_nonneg z)).trans_lt (by simpa using hz)
  have he := isUnit_one_sub_of_norm_lt_one hza
  have hi := Matrix.mul_nonsing_inv (1-z • a) ((Matrix.isUnit_iff_isUnit_det _).mp he)
  let V := (1-z • a)⁻¹*b
  let R := transfer a b c d z
  have hV : a*(z • V)+b = V := by
    have hiV : (1-z • a)*V = b := by
      dsimp only [V]
      rw [← Matrix.mul_assoc,hi,Matrix.one_mul]
    rw [Matrix.sub_mul,Matrix.one_mul,Matrix.smul_mul] at hiV
    rw [Matrix.mul_smul]
    linear_combination (norm := module) -hiV
  have hR : c*(z • V)+d = R := by
    dsimp only [R,transfer,V]
    rw [Matrix.mul_smul,← Matrix.mul_assoc]
    exact add_comm _ _
  let W : Matrix (n ⊕ n) (n ⊕ n) ℂ := Matrix.fromBlocks (z • V) 0 1 0
  let UW : Matrix (n ⊕ n) (n ⊕ n) ℂ := Matrix.fromBlocks V 0 R 0
  have hw : Matrix.fromBlocks a b c d * W = UW := by
    simp only [W,UW,Matrix.fromBlocks_multiply,Matrix.mul_one,Matrix.mul_zero,zero_add,hV,hR]
  have hgram : UWᴴ*UW = Wᴴ*W := by
    rw [← hw,Matrix.conjTranspose_mul]
    calc
      _ = Wᴴ*((Matrix.fromBlocks a b c d)ᴴ*Matrix.fromBlocks a b c d)*W := by noncomm_ring
      _ = _ := by rw [hU,Matrix.mul_one]
  have hg := congrArg Matrix.toBlocks₁₁ hgram
  simp only [UW,W,Matrix.fromBlocks_conjTranspose,Matrix.fromBlocks_multiply,
    Matrix.toBlocks_fromBlocks₁₁,Matrix.conjTranspose_one,Matrix.one_mul,
    Matrix.conjTranspose_smul,Matrix.smul_mul,Matrix.mul_smul,smul_smul] at hg
  have hsc : z*star z = (‖z‖^2 : ℝ) := by
    change z * (starRingEnd ℂ) z = _
    rw [mul_comm,← Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_norm_sq]
  rw [hsc] at hg
  have hg' : 1-Rᴴ*R = (1-‖z‖^2 : ℝ) • (Vᴴ*V) := by
    rw [sub_smul,one_smul]
    have hcast : ((‖z‖^2 : ℝ) : ℂ) • (Vᴴ*V) = (‖z‖^2 : ℝ) • (Vᴴ*V) := by
      ext i j; simp [Complex.real_smul]
    rw [hcast] at hg
    linear_combination (norm := module) -hg
  have hp : 0 ≤ (1-‖z‖^2 : ℝ) • (Vᴴ*V) := by
    apply smul_nonneg
    · nlinarith [norm_nonneg z]
    · exact (Matrix.posSemidef_conjTranspose_mul_self V).nonneg
  rw [← hg'] at hp
  exact norm_le_one_of_star_mul_le (sub_nonneg.mp hp)

end

open scoped BigOperators Matrix.Norms.L2Operator
open Set Filter Metric Topology
section
variable {n : Type u_176} [Fintype n] [DecidableEq n]

lemma meromorphic_matrix_det {M : ℂ → Matrix n n ℂ} {z : ℂ}
    (hM : ∀ i j, MeromorphicAt (fun w => M w i j) z) :
    MeromorphicAt (fun w => Matrix.det (M w)) z := by
  simp only [Matrix.det_apply']
  apply MeromorphicAt.fun_sum
  intro σ _
  exact (MeromorphicAt.const _ z).mul (MeromorphicAt.fun_prod (fun i _ => hM (σ i) i))

lemma meromorphic_matrix_adjugate {M : ℂ → Matrix n n ℂ} {z : ℂ}
    (hM : ∀ i j, MeromorphicAt (fun w => M w i j) z) (i j : n) :
    MeromorphicAt (fun w => (M w).adjugate i j) z := by
  simp only [Matrix.adjugate_apply]
  apply meromorphic_matrix_det
  intro k l
  by_cases hk : k = j
  · subst k
    simpa only [Matrix.updateRow_self] using MeromorphicAt.const ((Pi.single i (1:ℂ) : n → ℂ) l) z
  · simpa only [Matrix.updateRow_ne hk] using hM k l

lemma meromorphic_matrix_inverse {M : ℂ → Matrix n n ℂ} {z : ℂ}
    (hM : ∀ i j, MeromorphicAt (fun w => M w i j) z) (i j : n) :
    MeromorphicAt (fun w => (M w)⁻¹ i j) z := by
  simp only [Matrix.inv_def,Ring.inverse_eq_inv,Matrix.smul_apply,smul_eq_mul]
  exact (meromorphic_matrix_det hM).inv.mul (meromorphic_matrix_adjugate hM i j)

end

open Set Filter Metric Topology

lemma meromorphic_order_nonneg_of_disk_bound {f : ℂ → ℂ} {C : ℝ}
    (_hf : MeromorphicOn f Set.univ) (ha : AnalyticOnNhd ℂ f (ball 0 1))
    (hb : ∀ z ∈ ball 0 1, ‖f z‖ ≤ C) {x : ℂ} (hx : x ∈ closedBall 0 1) :
    0 ≤ meromorphicOrderAt f x := by
  by_cases hxi : x ∈ ball 0 1
  · exact (ha x hxi).meromorphicOrderAt_nonneg
  have hxc : x ∈ closure (ball (0:ℂ) 1) := by
    simpa only [closure_ball (0:ℂ) (by norm_num : (1:ℝ) ≠ 0)] using hx
  have : NeBot (𝓝[ball (0:ℂ) 1] x) := mem_closure_iff_nhdsWithin_neBot.mp hxc
  have hsub : ball (0:ℂ) 1 ⊆ {x}ᶜ := by
    intro z hz he
    exact hxi ((mem_singleton_iff.mp he) ▸ hz)
  by_contra hneg
  have ht := (tendsto_norm_cobounded_atTop.comp
    (tendsto_cobounded_of_meromorphicOrderAt_neg (lt_of_not_ge hneg))).mono_left
      (nhdsWithin_mono x hsub)
  obtain ⟨z,hz,hgt⟩ := ((show ∀ᶠ z in 𝓝[ball (0:ℂ) 1] x, z ∈ ball 0 1 from self_mem_nhdsWithin).and
    (ht.eventually (eventually_gt_atTop C))).exists
  exact not_lt_of_ge (hb z hz) hgt

lemma bounded_meromorphic_disk_extension {f : ℂ → ℂ} {C : ℝ}
    (hf : MeromorphicOn f Set.univ) (ha : AnalyticOnNhd ℂ f (ball 0 1))
    (hb : ∀ z ∈ ball 0 1, ‖f z‖ ≤ C) :
    ∃ g, AnalyticOnNhd ℂ g (closedBall 0 1) ∧ EqOn g f (ball 0 1) := by
  let g := toMeromorphicNFOn f Set.univ
  refine ⟨g,?_,?_⟩
  · intro x hx
    have hn := (hf x (mem_univ x)).meromorphicOrderAt_nonneg_iff_analyticAt_toMeromorphicNFAt.mp
      (meromorphic_order_nonneg_of_disk_bound hf ha hb hx)
    exact hn.congr (toMeromorphicNFOn_eq_toMeromorphicNFAt_on_nhds hf (mem_univ x)).symm
  · intro x hx
    rw [show g x = toMeromorphicNFAt f x x from
      toMeromorphicNFOn_eq_toMeromorphicNFAt hf (mem_univ x)]
    rw [toMeromorphicNFAt_eq_self.mpr (ha x hx).meromorphicNFAt]


end CompleteCrouzeix

end

end OAI
