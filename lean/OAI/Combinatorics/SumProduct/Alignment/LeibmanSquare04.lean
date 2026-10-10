import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.RationalQuotient01
import OAI.Combinatorics.SumProduct.Alignment.WeylInverse01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
section
open scoped commutatorElement Pointwise
namespace LeibmanSquare
open CubeFaces RationalQuotientFunctions
open scoped ComplexConjugate
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

 
noncomputable def balanced (H : Filtration G) (h0 : H.level 0 = ⊤) (Γ : Subgroup G)
    (F : C(G ⧸ Γ,ℂ)) (a b : G) (x : level H h0 1) : ℂ :=
  F (QuotientGroup.mk (a*x.val.1)) * conj (F (QuotientGroup.mk (b*x.val.2)))

lemma continuous_balanced (H : Filtration G) (h0 : H.level 0 = ⊤) (Γ : Subgroup G)
    (F : C(G ⧸ Γ,ℂ)) (a b : G) : Continuous (balanced H h0 Γ F a b) := by
  exact (F.continuous.comp (QuotientGroup.continuous_mk.comp
    (continuous_const.mul (continuous_fst.comp continuous_subtype_val)))).mul
      (continuous_star.comp (F.continuous.comp (QuotientGroup.continuous_mk.comp
        (continuous_const.mul (continuous_snd.comp continuous_subtype_val)))))

omit [IsTopologicalGroup G] in
lemma balanced_lattice (H : Filtration G) (h0 : H.level 0 = ⊤) (Γ : Subgroup G)
    (F : C(G ⧸ Γ,ℂ)) (a b : G) (x γ : level H h0 1)
    (hγ : γ ∈ (Γ.prod Γ).comap (level H h0 1).subtype) :
    balanced H h0 Γ F a b (x*γ) = balanced H h0 Γ F a b x := by
  change F (QuotientGroup.mk (a*(x.val.1*γ.val.1))) *
    conj (F (QuotientGroup.mk (b*(x.val.2*γ.val.2)))) = _
  rw [← mul_assoc,← mul_assoc]
  have he1 := QuotientGroup.mk_mul_of_mem (s := Γ) (a*x.val.1) hγ.1
  have he2 := QuotientGroup.mk_mul_of_mem (s := Γ) (b*x.val.2) hγ.2
  exact congrArg₂ (fun (u v : G ⧸ Γ) => F u * conj (F v)) he1 he2

omit [IsTopologicalGroup G] in
 

lemma balanced_last (H : Filtration G) (h0 : H.level 0 = ⊤) (Γ : Subgroup G)
    (F : C(G ⧸ Γ,ℂ)) (a b : G) (s : ℕ) (hs0 : 1 ≤ s)
    (hs : H.level (s+1) = ⊥) (χ : G → ℂ)
    (hχ : ∀ n ∈ H.level s, ‖χ n‖ = 1)
    (hw : ∀ n ∈ H.level s, ∀ x : G,
      F (QuotientGroup.mk (x*n)) = χ n * F (QuotientGroup.mk x))
    (x n : level H h0 1) (hn : n ∈ (restricted H h0).level s) :
    balanced H h0 Γ F a b (x*n) = balanced H h0 Γ F a b x := by
  change n.val ∈ level H h0 (max 1 s) at hn
  rw [max_eq_right hs0] at hn
  obtain ⟨hnS,he⟩ := (last_level H h0 s hs n.val).mp hn
  have hnχ : χ n.val.1 * conj (χ n.val.1) = 1 := by
    rw [Complex.mul_conj,Complex.normSq_eq_norm_sq,hχ _ hnS]
    norm_num
  change F (QuotientGroup.mk (a*(x.val.1*n.val.1))) *
    conj (F (QuotientGroup.mk (b*(x.val.2*n.val.2)))) = _
  rw [← he,← mul_assoc,← mul_assoc,hw _ hnS,hw _ hnS,map_mul]
  calc
    _ = (χ n.val.1 * conj (χ n.val.1)) * balanced H h0 Γ F a b x := by
      simp only [balanced]; ring
    _ = _ := by rw [hnχ,one_mul]

omit [IsTopologicalGroup G] in
lemma balanced_bound (H : Filtration G) (h0 : H.level 0 = ⊤) (Γ : Subgroup G)
    (F : C(G ⧸ Γ,ℂ)) (a b : G) (hF : ∀ x, ‖F x‖ ≤ 1) (x : level H h0 1) :
    ‖balanced H h0 Γ F a b x‖ ≤ 1 := by
  rw [balanced,norm_mul,RCLike.norm_conj]
  exact (mul_le_of_le_one_left (norm_nonneg _) (hF _)).trans (hF _)

 

theorem exists_reduced_observable (H : Filtration G) (h0 : H.level 0 = ⊤)
    (Γ : Subgroup G) (F : C(G ⧸ Γ,ℂ)) (a b : G) (hF : ∀ x, ‖F x‖ ≤ 1)
    (s : ℕ) (hs0 : 1 ≤ s) (hs : H.level (s+1) = ⊥) (χ : G → ℂ)
    (hχ : ∀ n ∈ H.level s, ‖χ n‖ = 1)
    (hw : ∀ n ∈ H.level s, ∀ x : G,
      F (QuotientGroup.mk (x*n)) = χ n * F (QuotientGroup.mk x)) :
    let R := restricted H h0
    let L := (Γ.prod Γ).comap (level H h0 1).subtype
    letI := last_normal H h0 hs0 hs
    let π := QuotientGroup.mk' (R.level s)
    ∃ Ψ : C(((level H h0 1) ⧸ R.level s) ⧸ L.map π,ℂ),
      (∀ x, ‖Ψ x‖ ≤ 1) ∧
      ∀ x : level H h0 1, Ψ (QuotientGroup.mk (π x)) = balanced H h0 Γ F a b x := by
  let R := restricted H h0
  let L := (Γ.prod Γ).comap (level H h0 1).subtype
  let := last_normal H h0 hs0 hs
  let B : C(level H h0 1,ℂ) := ⟨balanced H h0 Γ F a b,
    continuous_balanced H h0 Γ F a b⟩
  have hN := balanced_last H h0 Γ F a b s hs0 hs χ hχ hw
  have hL := balanced_lattice H h0 Γ F a b
  obtain ⟨Ψ,hΨ,_⟩ := existsUnique_normalDescend (R.level s) L B hN hL
  refine ⟨Ψ,?_,hΨ⟩
  intro x
  induction x using Quotient.inductionOn with | h y =>
    induction y using Quotient.inductionOn with | h z =>
      change ‖Ψ (QuotientGroup.mk (QuotientGroup.mk' (R.level s) z))‖ ≤ 1
      rw [hΨ]
      exact balanced_bound H h0 Γ F a b hF z

variable {A : Type*} [AddCommGroup A]

omit [IsTopologicalGroup G] in
 

lemma balanced_normalized (H : Filtration G) (h0 : H.level 0 = ⊤)
    (h1 : H.level 1 = ⊤) (Γ : Subgroup G) (F : C(G ⧸ Γ,ℂ))
    {f : A → G} (hf : Polynomial H 0 f) (t : A) (a b γ δ : G)
    (hγ : γ ∈ Γ) (hδ : δ ∈ Γ) (ha : f 0 = a*γ) (hb : f t = b*δ) (n : A) :
    balanced H h0 Γ F a b
      (restrictedConj H h0 h1 γ δ (normalizedPair H h0 hf t n)) =
      F (QuotientGroup.mk (f n)) * conj (F (QuotientGroup.mk (f (n+t)))) := by
  change F (QuotientGroup.mk (a*MulAut.conj γ ((f 0)⁻¹*f n))) *
    conj (F (QuotientGroup.mk (b*MulAut.conj δ ((f t)⁻¹*f (n+t))))) = _
  rw [orbit_normalization Γ ha hγ,orbit_normalization Γ hb hδ]

end LeibmanSquare

namespace LeibmanSquare
open CubeFaces MeasureTheory
open scoped ComplexConjugate
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

 

theorem reduced_observable_mean_zero (H : Filtration G) (h0 : H.level 0 = ⊤)
    (h1 : H.level 1 = ⊤) (Γ : Subgroup G) (F : C(G ⧸ Γ,ℂ)) (a b : G)
    (s : ℕ) (hs2 : 2 ≤ s) (hs : H.level (s+1) = ⊥) (χ : G → ℂ)
    (hw : ∀ n ∈ H.level s, ∀ x : G,
      F (QuotientGroup.mk (x*n)) = χ n * F (QuotientGroup.mk x))
    (z : G) (hz : z ∈ H.level s) (hχz : χ z ≠ 1) :
    let R := restricted H h0
    let L := (Γ.prod Γ).comap (level H h0 1).subtype
    letI := last_normal H h0 (by omega : 1 ≤ s) hs
    let π := QuotientGroup.mk' (R.level s)
    let X := ((level H h0 1) ⧸ R.level s) ⧸ L.map π
    letI : MeasurableSpace X := borel X
    ∀ (μ : Measure X), SMulInvariantMeasure ((level H h0 1) ⧸ R.level s) X μ →
      ∀ Ψ : C(X,ℂ),
        (∀ x : level H h0 1, Ψ (QuotientGroup.mk (π x)) = balanced H h0 Γ F a b x) →
        (∫ x, Ψ x ∂μ) = 0 := by
  let R := restricted H h0
  let L := (Γ.prod Γ).comap (level H h0 1).subtype
  let := last_normal H h0 (by omega : 1 ≤ s) hs
  let π := QuotientGroup.mk' (R.level s)
  let X := ((level H h0 1) ⧸ R.level s) ⧸ L.map π
  let : MeasurableSpace X := borel X
  let : BorelSpace X := ⟨rfl⟩
  dsimp only
  intro μ hμ Ψ hΨ
  let := hμ
  have hzC : ∀ x : G, Commute z x := by
    intro x
    apply commutatorElement_eq_one_iff_commute.mp
    have hx : x ∈ H.level 1 := by rw [h1]; trivial
    have hc := H.commutator_le s 1 (Subgroup.commutator_mem_commutator hz hx)
    simpa only [hs,Subgroup.mem_bot] using hc
  let Z : level H h0 1 := ⟨(z,1),⟨H.antitone (by omega) hz,
    (H.level 1).one_mem, by simpa using (H.level 2).inv_mem (H.antitone hs2 hz)⟩⟩
  have hweight : ∀ x : X, Ψ (π Z • x) = χ z * Ψ x := by
    intro x
    induction x using Quotient.inductionOn with | h y =>
      induction y using Quotient.inductionOn with | h v =>
        change Ψ (QuotientGroup.mk (π Z * π v)) = χ z * Ψ (QuotientGroup.mk (π v))
        rw [← map_mul,hΨ,hΨ]
        change F (QuotientGroup.mk (a*(z*v.val.1))) *
          conj (F (QuotientGroup.mk (b*(1*v.val.2)))) =
            χ z * (F (QuotientGroup.mk (a*v.val.1)) * conj (F (QuotientGroup.mk (b*v.val.2))))
        rw [one_mul,(hzC v.val.1).eq,← mul_assoc,hw z hz,mul_assoc]
  have hi := integral_smul_eq_self (μ := μ) (fun x => Ψ x) (g := π Z)
  simp only [hweight,integral_const_mul] at hi
  have he : (χ z - 1) * (∫ x, Ψ x ∂μ) = 0 := by rw [sub_mul,one_mul,hi,sub_self]
  exact (mul_eq_zero.mp he).resolve_left (sub_ne_zero.mpr hχz)
end LeibmanSquare

namespace SquareDifferences
open PolynomialWeyl
open scoped BigOperators ComplexConjugate
noncomputable section
 

theorem density_of_large_average {ι : Type*} (S : Finset ι) (hS : S.Nonempty)
    (f : ι → ℝ) (t : ℝ) (ht : 0 ≤ t) (hf : ∀ x ∈ S, f x ≤ 1)
    (havg : 2 * t ≤ 𝔼 x ∈ S, f x) :
    t * S.card ≤ ((S.filter (fun x => t ≤ f x)).card : ℝ) := by
  classical
  have h : (∑ x ∈ S, f x) ≤ ∑ x ∈ S, (t + if t ≤ f x then (1 : ℝ) else 0) := by
    apply Finset.sum_le_sum
    intro x hx
    split_ifs with htx
    · linarith [hf x hx]
    · linarith
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
    Finset.sum_boole] at h
  rw [Finset.expect_eq_sum_div_card] at havg
  have hc : 0 < (S.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hS)
  have havg' := (le_div_iff₀ hc).mp havg
  nlinarith

 

theorem exists_dense_derivatives {N H : ℕ} (hN : 0 < N) (hH : 0 < H)
    (f : ℕ → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) (δ : ℝ) (hδ : 0 < δ)
    (hlarge : δ ≤ ‖mean N f‖) (hboundary : 4 * (H : ℝ) / N ≤ δ ^ 2 / 2) :
    ∃ b ∈ Finset.range H, ∃ S : Finset ℕ,
      (∀ a ∈ S, a < H) ∧ δ ^ 2 / 4 * H ≤ (S.card : ℝ) ∧
      (∀ a ∈ S, δ ^ 2 / 4 ≤ ‖mean N (derivative a b f)‖) := by
  classical
  have hv := van_der_corput hN hH f hf
  rw [Finset.expect_comm] at hv
  have havg : δ ^ 2 / 2 ≤
      𝔼 b ∈ Finset.range H, 𝔼 a ∈ Finset.range H, ‖mean N (derivative a b f)‖ := by
    nlinarith [norm_nonneg (mean N f)]
  have hs := Finset.nonempty_range_iff.mpr (Nat.ne_of_gt hH)
  obtain ⟨b, hb, hbavg⟩ := Finset.exists_le_of_le_expect hs havg
  let t := δ ^ 2 / 4
  let S := (Finset.range H).filter (fun a => t ≤ ‖mean N (derivative a b f)‖)
  refine ⟨b, hb, S, ?_, ?_, ?_⟩
  · intro a ha
    exact Finset.mem_range.mp (Finset.mem_filter.mp ha).1
  · have h := density_of_large_average (Finset.range H) hs
      (fun a => ‖mean N (derivative a b f)‖) t (by dsimp [t]; positivity)
      (fun a _ => norm_mean_le_one _ (norm_derivative_le_one a b f hf))
      (by dsimp [t]; linarith)
    simpa only [Finset.card_range] using h
  · intro a ha
    exact (Finset.mem_filter.mp ha).2

end
end SquareDifferences

namespace LeibmanSquare
open CubeFaces PolynomialWeyl
open scoped BigOperators ComplexConjugate
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

 

theorem dense_reduced_square_orbits_tracked (H : Filtration G) (h0 : H.level 0 = ⊤)
    (h1 : H.level 1 = ⊤) (Γ : Subgroup G) (F : C(G ⧸ Γ,ℂ))
    (hF : ∀ x, ‖F x‖ ≤ 1) (s : ℕ) (hs2 : 2 ≤ s)
    (hs : H.level (s+1) = ⊥) (χ : G → ℂ)
    (hχ : ∀ n ∈ H.level s, ‖χ n‖ = 1)
    (hw : ∀ n ∈ H.level s, ∀ x : G,
      F (QuotientGroup.mk (x*n)) = χ n * F (QuotientGroup.mk x))
    (C : Set G) (hC : ∀ g : G, ∃ c ∈ C, c⁻¹*g ∈ Γ)
    (f : ℤ → G) (hf : Polynomial H 0 f)
    (N T : ℕ) (hN : 0 < N) (hT : 0 < T) (δ : ℝ) (hδ : 0 < δ)
    (hlarge : δ ≤ ‖mean N (fun n => F (QuotientGroup.mk (f n)))‖)
    (hboundary : 4 * (T : ℝ) / N ≤ δ^2 / 2) :
    let R := restricted H h0
    let L := (Γ.prod Γ).comap (level H h0 1).subtype
    letI := last_normal H h0 (by omega : 1 ≤ s) hs
    let π := QuotientGroup.mk' (R.level s)
    let Q := mapFiltration R π
    ∃ b ∈ Finset.range T, ∃ S : Finset ℕ,
      (∀ a ∈ S, a < T) ∧ δ^2 / 4 * T ≤ (S.card : ℝ) ∧
      ∀ a ∈ S, ∃ u ∈ C, ∃ v ∈ C,
      ∃ Ψ : C(((level H h0 1) ⧸ R.level s) ⧸ L.map π,ℂ),
      ∃ p : ℤ → (level H h0 1) ⧸ R.level s,
      ∃ γ ∈ Γ, ∃ ε ∈ Γ,
        f a = u*γ ∧ f b = v*ε ∧
        (∀ n : ℤ, ∃ x : level H h0 1, p n = π x ∧
          x.val = (u⁻¹*f (n+a)*γ⁻¹, v⁻¹*f (n+b)*ε⁻¹)) ∧
        (∀ x, ‖Ψ x‖ ≤ 1) ∧
        (∀ x : level H h0 1, Ψ (QuotientGroup.mk (π x)) = balanced H h0 Γ F u v x) ∧
        Polynomial Q 0 p ∧
        (∀ ts : List ℤ, s ≤ ts.length → ∀ n, iterDiff ts p n = 1) ∧
        (∀ n : ℤ, Ψ (QuotientGroup.mk (p n)) =
          F (QuotientGroup.mk (f (n+a))) * conj (F (QuotientGroup.mk (f (n+b))))) ∧
        δ^2/4 ≤ ‖mean N (fun n => Ψ (QuotientGroup.mk (p n)))‖ := by
  classical
  let R := restricted H h0
  let L := (Γ.prod Γ).comap (level H h0 1).subtype
  let := last_normal H h0 (by omega : 1 ≤ s) hs
  let π := QuotientGroup.mk' (R.level s)
  let Q := mapFiltration R π
  obtain ⟨b,hb,S,hST,hSc,hSd⟩ := SquareDifferences.exists_dense_derivatives hN hT
    (fun n => F (QuotientGroup.mk (f n))) (fun n => hF _) δ hδ hlarge hboundary
  refine ⟨b,hb,S,hST,hSc,?_⟩
  intro a ha
  let f' : ℤ → G := fun n => f (n+a)
  have hf' : Polynomial H 0 f' := by
    intro ts n
    simpa only [f',iterDiff_shift] using hf ts (n+a)
  obtain ⟨u,hu,hγ⟩ := hC (f a)
  obtain ⟨v,hv,hε⟩ := hC (f b)
  let γ := u⁻¹*f a
  let ε := v⁻¹*f b
  have hfa : f' 0 = u*γ := by simp [f',γ]
  have hfb : f' ((b:ℤ)-a) = v*ε := by simp [f',ε]
  obtain ⟨Ψ,hΨBound,hΨ⟩ := exists_reduced_observable H h0 Γ F u v hF s
    (by omega) hs χ hχ hw
  let p : ℤ → (level H h0 1) ⧸ R.level s := fun n =>
    π (restrictedConj H h0 h1 γ ε (normalizedPair H h0 hf' ((b:ℤ)-a) n))
  have hp := reduced_pair_polynomial H h0 h1 (by omega : 1 ≤ s) hs hf' ((b:ℤ)-a) γ ε
  have heval : ∀ n : ℤ, Ψ (QuotientGroup.mk (p n)) =
      F (QuotientGroup.mk (f (n+a))) * conj (F (QuotientGroup.mk (f (n+b)))) := by
    intro n
    rw [show p n = π (restrictedConj H h0 h1 γ ε
      (normalizedPair H h0 hf' ((b:ℤ)-a) n)) from rfl,hΨ]
    rw [balanced_normalized H h0 h1 Γ F hf' ((b:ℤ)-a) u v γ ε hγ hε hfa hfb]
    dsimp only [f']
    congr 3
    abel_nf
  have hlift : ∀ n : ℤ, ∃ x : level H h0 1, p n = π x ∧
      x.val = (u⁻¹*f (n+a)*γ⁻¹, v⁻¹*f (n+b)*ε⁻¹) := by
    intro n
    refine ⟨restrictedConj H h0 h1 γ ε
      (normalizedPair H h0 hf' ((b:ℤ)-a) n), rfl, ?_⟩
    change (γ * ((f' 0)⁻¹ * f' n) * γ⁻¹,
      ε * ((f' ((b:ℤ)-a))⁻¹ * f' (n+((b:ℤ)-a))) * ε⁻¹) = _
    rw [hfa, hfb]
    have hn : n + ((b:ℤ)-a) + a = n+b := by abel
    simp [f', mul_inv_rev, mul_assoc, hn]
  refine ⟨u,hu,v,hv,Ψ,p,γ,hγ,ε,hε,by simpa [f'] using hfa,
    by simpa [f'] using hfb,hlift,hΨBound,hΨ,hp.1,hp.2,heval,?_⟩
  have he : mean N (fun n => Ψ (QuotientGroup.mk (p n))) =
      mean N (derivative a b (fun n => F (QuotientGroup.mk (f n)))) := by
    apply Finset.expect_congr rfl
    intro n hn
    simp only [derivative,heval,Nat.cast_add]
  rw [he]
  exact hSd a ha
end LeibmanSquare

end
end
end
end

end OAI
