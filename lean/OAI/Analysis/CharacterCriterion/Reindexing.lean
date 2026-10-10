import OAI.Analysis.CharacterCriterion.NormUltrapower

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [KirchbergRordam.GenericRW.Size]
local notation "rankNum" => KirchbergRordam.GenericRW.Size.n
variable [KirchbergRordam.GenericRW.PauliData]
omit [KirchbergRordam.GenericRW.Size] [KirchbergRordam.GenericRW.PauliData]
open Filter Topology BoundedContinuousFunction

open Filter Topology
namespace KirchbergRordam.Reindex


theorem diagonal_select {ι : Type*} [Countable ι] (ω : Filter ℕ) [NeBot ω]
    (f : ι → ℕ → ℕ → ℝ)
    (hf : ∀ i s, Tendsto (f i s) ω (𝓝 0)) :
    ∃ k : ℕ → ℕ, ∀ i, Tendsto (fun s => f i s (k s)) atTop (𝓝 0) := by
  classical
  let := Encodable.ofCountable ι
  have good (s : ℕ) : ∃ l, ∀ i, Encodable.encode i ≤ s → |f i s l| < 1 / ((s:ℝ)+1) := by
    have hfin : {i : ι | Encodable.encode i ≤ s}.Finite :=
      (Set.finite_Iic s).preimage Encodable.encode_injective.injOn
    have he : ∀ᶠ l in ω, ∀ i ∈ {i : ι | Encodable.encode i ≤ s},
        |f i s l| < 1 / ((s:ℝ)+1) := hfin.eventually_all.mpr fun i _ => by
      have hp : (0:ℝ) < 1 / ((s:ℝ)+1) := by positivity
      simpa only [Real.dist_eq, sub_zero] using
        (tendsto_order.1 ((hf i s).abs)).2 _ (by simpa using hp)
    exact he.exists
  choose k hk using good
  refine ⟨k, fun i => ?_⟩
  apply squeeze_zero_norm' (a := fun s : ℕ => 1 / ((s:ℝ)+1))
  · filter_upwards [eventually_ge_atTop (Encodable.encode i)] with s hs
    simpa only [Real.norm_eq_abs] using (hk s i hs).le
  · exact tendsto_one_div_add_atTop_nhds_zero_nat
end KirchbergRordam.Reindex

namespace KirchbergRordam.NormUltrapower
open Filter Topology TopologicalSpace
open scoped CStarAlgebra
variable {A : Type*} [CStarAlgebra A]
lemma quotient_eq_iff (ω : Ultrafilter ℕ) (x y : BoundedSeq A) :
    quotientMap ω x = quotientMap ω y ↔
      Tendsto (fun n => ‖x n - y n‖) (ω : Filter ℕ) (𝓝 0) := by
  change Ideal.Quotient.mk (nullIdeal ω) x = Ideal.Quotient.mk (nullIdeal ω) y ↔ _
  rw [Ideal.Quotient.eq, mem_nullIdeal]
  rfl

def reindexed (k : ℕ → ℕ) (x : BoundedSeq A) : BoundedSeq A :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete (fun n => x (k n)) ‖x‖
    (fun n => x.norm_coe_le_norm (k n))
@[simp] lemma reindexed_apply (k : ℕ → ℕ) (x : BoundedSeq A) (n : ℕ) :
    reindexed k x n = x (k n) := rfl

inductive ReindexTest (S : Type*)
  | add (x y : S) | mul (x y : S) | adjoint (x : S)
  | zero | one | norm (x : S) | central (x : S) (j : ℕ)
  | commute (x : S) (j : ℕ) | imag
  deriving Countable


theorem countable_reindex {S : Type*} [Ring S] [StarRing S] [Countable S]
    [SeparableSpace A] (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ cofinite)
    (φ : S →+* Algebra A ω) (hφ : ∀ x, φ (star x) = star (φ x))
    (hc : ∀ x, φ x ∈ centralSubalgebra ω)
    (j : S) (hj : φ j = diagonal ω (algebraMap ℂ A Complex.I))
    (b : ℕ → BoundedSeq A) :
    ∃ θ : S →+* CentralAlgebra A ω,
      (∀ x, θ (star x) = star (θ x)) ∧
      (∀ x, ‖θ x‖ = ‖φ x‖) ∧
      (θ j : Algebra A ω) = diagonal ω (algebraMap ℂ A Complex.I) ∧
      ∀ x n, Commute (θ x : Algebra A ω) (quotientMap ω (b n)) := by
  classical
  have hex (x : S) : ∃ u : BoundedSeq A, quotientMap ω u = φ x :=
    Ideal.Quotient.mk_surjective _
  choose u hu using hex
  let a : ℕ → A := TopologicalSpace.denseSeq A
  have ha : DenseRange a := TopologicalSpace.denseRange_denseSeq A
  let test : ReindexTest S → ℕ → ℕ → ℝ
    | .add x y, _, l => ‖u (x+y) l - (u x l + u y l)‖
    | .mul x y, _, l => ‖u (x*y) l - u x l * u y l‖
    | .adjoint x, _, l => ‖u (star x) l - star (u x l)‖
    | .zero, _, l => ‖u 0 l - 0‖
    | .one, _, l => ‖u 1 l - 1‖
    | .norm x, _, l => ‖u x l‖ - ‖φ x‖
    | .central x n, _, l => ‖u x l * a n - a n * u x l‖
    | .commute x n, s, l => ‖u x l * b n s - b n s * u x l‖
    | .imag, _, l => ‖u j l - algebraMap ℂ A Complex.I‖
  have ht (i : ReindexTest S) (s : ℕ) : Tendsto (test i s) (ω : Filter ℕ) (𝓝 0) := by
    have hn (x y : BoundedSeq A) (h : quotientMap ω x = quotientMap ω y) :=
      (quotient_eq_iff ω x y).mp h
    have hcent x : ∀ c : A, Tendsto (fun l => ‖u x l * c - c * u x l‖)
        (ω : Filter ℕ) (𝓝 0) := (mk_mem_central_iff ω (u x)).mp (by rw [hu]; exact hc x)
    cases i with
    | add x y => exact hn (u (x+y)) (u x + u y) (by simp only [hu, map_add])
    | mul x y => exact hn (u (x*y)) (u x * u y) (by simp only [hu, map_mul])
    | adjoint x => exact hn (u (star x)) (star (u x)) (by simp only [hu, map_star, hφ])
    | zero => exact hn (u 0) 0 (by simp only [hu, map_zero])
    | one => exact hn (u 1) 1 (by simp only [hu, map_one])
    | norm x =>
      have he : normLimit ω (u x) = ‖φ x‖ := by rw [← hu]; exact (norm_mk_eq ω (u x)).symm
      simpa only [he, sub_self] using (tendsto_norm ω (u x)).sub_const ‖φ x‖
    | central x n => exact hcent x (a n)
    | commute x n => exact hcent x (b n s)
    | imag => exact hn (u j) (constantSeq (algebraMap ℂ A Complex.I)) (by rw [hu,hj]; rfl)
  obtain ⟨k,hk⟩ := Reindex.diagonal_select (ω : Filter ℕ) test ht
  have hfree : (ω : Filter ℕ) ≤ atTop := by simpa only [Nat.cofinite_eq_atTop] using hω
  have hk' (i : ReindexTest S) : Tendsto (fun s => test i s (k s)) (ω : Filter ℕ) (𝓝 0) :=
    (hk i).mono_left hfree
  let v : S → BoundedSeq A := fun x => reindexed k (u x)
  let g : S → Algebra A ω := fun x => quotientMap ω (v x)
  have heq (x y : BoundedSeq A)
      (h : Tendsto (fun s => ‖x s - y s‖) (ω : Filter ℕ) (𝓝 0)) :
      quotientMap ω x = quotientMap ω y := (quotient_eq_iff ω x y).mpr h
  have hadd (x y : S) : g (x+y) = g x + g y := by
    change quotientMap ω (v (x+y)) = _
    rw [← map_add]
    exact heq _ _ (hk' (.add x y))
  have hmul (x y : S) : g (x*y) = g x * g y := by
    change quotientMap ω (v (x*y)) = _
    rw [← map_mul]
    exact heq _ _ (hk' (.mul x y))
  have hstar (x : S) : g (star x) = star (g x) := by
    change quotientMap ω (v (star x)) = _
    rw [← map_star]
    exact heq _ _ (hk' (.adjoint x))
  have hzero : g 0 = 0 := by
    rw [← map_zero (quotientMap ω)]
    exact heq _ _ (hk' .zero)
  have hone : g 1 = 1 := by
    rw [← map_one (quotientMap ω)]
    exact heq _ _ (hk' .one)
  have hgNorm (x : S) : ‖g x‖ = ‖φ x‖ := by
    change ‖quotientMap ω (v x)‖ = _
    change ‖Ideal.Quotient.mk (nullIdeal ω) (v x)‖ = _
    rw [norm_mk_eq]
    apply tendsto_nhds_unique (tendsto_norm ω (v x))
    simpa only [test, v, reindexed_apply, sub_add_cancel, zero_add] using (hk' (.norm x)).add_const ‖φ x‖
  have hgCentral (x : S) : g x ∈ centralSubalgebra ω := by
    rw [mem_central_iff]
    intro c
    refine ha.induction_on c (p := fun c => diagonal ω c * g x = g x * diagonal ω c)
      (isClosed_eq (by fun_prop) (by fun_prop)) ?_
    intro n
    have he := heq (v x * constantSeq (a n)) (constantSeq (a n) * v x) (hk' (.central x n))
    change quotientMap ω (constantSeq (a n)) * quotientMap ω (v x) =
      quotientMap ω (v x) * quotientMap ω (constantSeq (a n))
    simpa only [map_mul] using he.symm
  let θ : S →+* CentralAlgebra A ω :=
    { toFun := fun x => ⟨g x, hgCentral x⟩
      map_zero' := Subtype.ext hzero
      map_one' := Subtype.ext hone
      map_add' := fun x y => Subtype.ext (hadd x y)
      map_mul' := fun x y => Subtype.ext (hmul x y) }
  refine ⟨θ, (fun x => Subtype.ext (hstar x)), hgNorm, ?_, ?_⟩
  · exact heq (v j) (constantSeq (algebraMap ℂ A Complex.I)) (hk' .imag)
  · intro x n
    have he := heq (v x * b n) (b n * v x) (hk' (.commute x n))
    exact (show g x * quotientMap ω (b n) = quotientMap ω (b n) * g x from
      by simpa only [map_mul] using he)
end KirchbergRordam.NormUltrapower
namespace KirchbergRordam.RationalDense
open Set Topology TopologicalSpace
variable {A : Type*} [CStarAlgebra A]
local instance : Algebra ℚ A := Algebra.compHom A (algebraMap ℚ ℂ)


def stage (s : Set A) : ℕ → Set A
  | 0 => s ∪ Set.range (algebraMap ℚ A)
  | n+1 => stage s n ∪ (fun p : A×A=>p.1+p.2) '' (stage s n ×ˢ stage s n) ∪
      (fun p : A×A=>p.1*p.2) '' (stage s n ×ˢ stage s n) ∪ star '' stage s n
lemma stage_step (s : Set A) (n : ℕ) : stage s n ⊆ stage s (n+1) :=
  fun _ hx => Or.inl (Or.inl (Or.inl hx))
lemma stage_mono (s : Set A) : Monotone (stage s) := monotone_nat_of_le_succ (stage_step s)
lemma stage_countable {s : Set A} (hs : s.Countable) (n : ℕ) : (stage s n).Countable := by
  induction n with
  | zero => exact hs.union (Set.countable_range _)
  | succ n ih => exact ((ih.union ((ih.prod ih).image _)).union
      ((ih.prod ih).image _)).union (ih.image _)
def termAlgebra (s : Set A) : StarSubalgebra ℚ A where
  carrier := ⋃ n, stage s n
  zero_mem' := mem_iUnion.mpr ⟨0,Or.inr ⟨0,map_zero _⟩⟩
  one_mem' := mem_iUnion.mpr ⟨0,Or.inr ⟨1,map_one _⟩⟩
  add_mem' := by
    intro a b ha hb
    obtain ⟨n,hn⟩ := mem_iUnion.mp ha
    obtain ⟨m,hm⟩ := mem_iUnion.mp hb
    exact mem_iUnion.mpr ⟨max n m + 1,Or.inl (Or.inl (Or.inr
      ⟨(a,b),⟨stage_mono s (le_max_left _ _) hn,stage_mono s (le_max_right _ _) hm⟩,rfl⟩))⟩
  mul_mem' := by
    intro a b ha hb
    obtain ⟨n,hn⟩ := mem_iUnion.mp ha
    obtain ⟨m,hm⟩ := mem_iUnion.mp hb
    exact mem_iUnion.mpr ⟨max n m + 1,Or.inl (Or.inr
      ⟨(a,b),⟨stage_mono s (le_max_left _ _) hn,stage_mono s (le_max_right _ _) hm⟩,rfl⟩)⟩
  algebraMap_mem' z := mem_iUnion.mpr ⟨0,Or.inr ⟨z,rfl⟩⟩
  star_mem' := by
    intro a ha
    obtain ⟨n,hn⟩ := mem_iUnion.mp ha
    exact mem_iUnion.mpr ⟨n+1,Or.inr ⟨a,hn,rfl⟩⟩

lemma term_countable {s : Set A} (hs : s.Countable) : (termAlgebra s : Set A).Countable :=
  Set.countable_iUnion (stage_countable hs)
lemma subset_term (s : Set A) : s ⊆ termAlgebra s :=
  fun _ ha => mem_iUnion.mpr ⟨0,Or.inl ha⟩

theorem exists_countable_dense_star [SeparableSpace A] :
    ∃ S : StarSubalgebra ℚ A, (S : Set A).Countable ∧ Dense (S : Set A) ∧
      algebraMap ℂ A Complex.I ∈ S := by
  obtain ⟨s,hc,hd⟩ := exists_countable_dense A
  refine ⟨termAlgebra (insert (algebraMap ℂ A Complex.I) s),
    term_countable (hc.insert _), hd.mono ?_, subset_term _ (mem_insert _ _)⟩
  exact fun a ha => subset_term _ (mem_insert_of_mem _ ha)
end KirchbergRordam.RationalDense
open Topology
namespace KirchbergRordam.RationalDense
variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
local instance (C : Type*) [CStarAlgebra C] : Algebra ℚ C :=
  Algebra.compHom C (algebraMap ℚ ℂ)


theorem extend_complex (S : StarSubalgebra ℚ A) (hS : Dense (S : Set A))
    (f : S →+* B) (hf : UniformContinuous f)
    (hstar : ∀ x, f (star x) = star (f x))
    (hI : algebraMap ℂ A Complex.I ∈ S)
    (hfI : f ⟨algebraMap ℂ A Complex.I,hI⟩ = algebraMap ℂ B Complex.I) :
    ∃ g : A →⋆ₐ[ℂ] B, ∀ x : S, g x = f x := by
  let i : S →+* A := S.subtype.toRingHom
  have ui : IsUniformInducing i := isometry_subtype_coe.isUniformInducing
  have di : DenseRange i := hS.denseRange_val
  let g : A →+* B := IsDenseInducing.extendRingHom ui di hf
  have hg : Continuous g := (uniformContinuous_uniformly_extend ui di hf).continuous
  have he (x : S) : g x = f x :=
    IsDenseInducing.extend_eq (ui.isDenseInducing di) hf.continuous x
  have hs (x : A) : g (star x) = star (g x) := by
    refine di.induction_on x (p := fun x => g (star x) = star (g x))
      (isClosed_eq (hg.comp continuous_star) (continuous_star.comp hg)) ?_
    intro x
    change g (↑(star x) : A) = star (g (x : A))
    rw [he,he,hstar]
  have hgi : g (algebraMap ℂ A Complex.I) = algebraMap ℂ B Complex.I :=
    (he ⟨_,hI⟩).trans hfI
  have hr (r : ℝ) : g (algebraMap ℂ A (r:ℂ)) = algebraMap ℂ B (r:ℂ) := by
    refine (Rat.denseRange_cast (𝕜 := ℝ)).induction_on r
      (p := fun r => g (algebraMap ℂ A (r:ℂ)) = algebraMap ℂ B (r:ℂ))
      (isClosed_eq (hg.comp ((continuous_algebraMap ℂ A).comp Complex.continuous_ofReal))
        ((continuous_algebraMap ℂ B).comp Complex.continuous_ofReal)) ?_
    intro q
    change g (algebraMap ℂ A ((q : ℝ) : ℂ)) = algebraMap ℂ B ((q : ℝ) : ℂ)
    rw [Complex.ofReal_ratCast]
    exact g.map_rat_algebraMap q
  have hcomplex (z : ℂ) : g (algebraMap ℂ A z) = algebraMap ℂ B z := by
    conv_lhs => rw [← Complex.re_add_im z]
    simp only [map_add,map_mul,hr,hgi]
    rw [← map_mul, ← map_add, Complex.re_add_im]
  exact ⟨{ g with map_star' := hs, commutes' := hcomplex }, he⟩
end KirchbergRordam.RationalDense

namespace KirchbergRordam.NormUltrapower
open Topology TopologicalSpace
open scoped CStarAlgebra

theorem relative_commuting_copy {A D E : Type*}
    [CStarAlgebra A] [CStarAlgebra D] [CStarAlgebra E]
    [SeparableSpace A] [SeparableSpace D] [SeparableSpace E]
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ Filter.cofinite)
    (φ : D →⋆ₐ[ℂ] CentralAlgebra A ω)
    (ψ : E →⋆ₐ[ℂ] CentralAlgebra A ω) :
    ∃ θ : D →⋆ₐ[ℂ] CentralAlgebra A ω,
      ∀ d e, Commute (θ d) (ψ e) := by
  classical
  let : _root_.Algebra ℚ D := Algebra.compHom D (algebraMap ℚ ℂ)
  obtain ⟨S,hcount,hden,hI⟩ := RationalDense.exists_countable_dense_star (A := D)
  let : Countable S := hcount.to_subtype
  let Φ : D →⋆ₐ[ℂ] Algebra A ω := (centralSubalgebra ω).subtype.comp φ
  let f : S →+* Algebra A ω := Φ.toRingHom.comp S.subtype.toRingHom
  have hfstar (x : S) : f (star x) = star (f x) := map_star Φ (x:D)
  have hfcent (x : S) : f x ∈ centralSubalgebra ω := (φ (x:D)).property
  have hfI : f ⟨_,hI⟩ = diagonal ω (algebraMap ℂ A Complex.I) := by
    change Φ (algebraMap ℂ D Complex.I) = _
    exact (Φ.commutes Complex.I).trans ((diagonal ω).commutes Complex.I).symm
  let e : ℕ → E := denseSeq E
  have he : DenseRange e := denseRange_denseSeq E
  have hbex (n : ℕ) : ∃ b : BoundedSeq A, quotientMap ω b = (ψ (e n) : Algebra A ω) :=
    Ideal.Quotient.mk_surjective _
  choose b hb using hbex
  obtain ⟨g,hgs,hgn,hgi,hgc⟩ := countable_reindex ω hω f hfstar hfcent ⟨_,hI⟩ hfI b
  have hbound (x : S) : ‖g x‖ ≤ ‖x‖ := by
    rw [hgn]
    exact NonUnitalStarAlgHom.norm_apply_le Φ (x:D)
  have hLip : LipschitzWith 1 g := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [dist_eq_norm, ← map_sub, NNReal.coe_one, one_mul]
    exact hbound (x-y)
  have hgi' : g ⟨_,hI⟩ = algebraMap ℂ (CentralAlgebra A ω) Complex.I := by
    apply Subtype.ext
    exact hgi.trans ((diagonal ω).commutes Complex.I)
  obtain ⟨θ,hθ⟩ := RationalDense.extend_complex S hden g hLip.uniformContinuous hgs hI hgi'
  refine ⟨θ, fun d e' => ?_⟩
  change θ d * ψ e' = ψ e' * θ d
  have hθc : Continuous θ := map_continuous θ
  have hψc : Continuous ψ := map_continuous ψ
  refine hden.denseRange_val.induction_on d
    (p := fun d => θ d * ψ e' = ψ e' * θ d)
    (isClosed_eq (hθc.mul continuous_const) (continuous_const.mul hθc)) ?_
  intro x
  rw [hθ]
  refine he.induction_on e' (p := fun e' => g x * ψ e' = ψ e' * g x)
    (isClosed_eq (continuous_const.mul hψc) (hψc.mul continuous_const)) ?_
  intro n
  apply Subtype.ext
  change (g x : Algebra A ω) * (ψ (e n) : Algebra A ω) =
    (ψ (e n) : Algebra A ω) * (g x : Algebra A ω)
  simpa only [hb] using (hgc x n).eq
end KirchbergRordam.NormUltrapower
end

end OAI
