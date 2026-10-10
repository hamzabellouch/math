import Mathlib

namespace OAI

/-! Compact-power rigidity, centralizers and uniqueness of one-parameter subgroups. -/

noncomputable section
open scoped Manifold ContDiff Topology BigOperators commutatorElement
open Function Set Manifold Topology Filter

namespace RawCompactNilpotent

def NoCompactPowers (G : Type*) [Group G] [TopologicalSpace G] : Prop :=
  ∀ g : G, ∀ K : Set G, IsCompact K → (∀ n : ℕ, g^n ∈ K) → g = 1

def CompactConjugacyCentral (G : Type*) [Group G] [TopologicalSpace G] : Prop :=
  ∀ g : G, ∀ K : Set G, IsCompact K → (∀ x : G, x*g*x⁻¹ ∈ K) → g ∈ Subgroup.center G

lemma eq_zero_of_compact_nsmul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : E) (K : Set E) (hK : IsCompact K) (hv : ∀ n : ℕ, n • v ∈ K) : v = 0 := by
  obtain ⟨B,hB⟩ := hK.isBounded.exists_norm_le
  by_contra h
  have hp : 0 < ‖v‖ := norm_pos_iff.mpr h
  obtain ⟨n,hn⟩ := exists_nat_gt (B / ‖v‖)
  have hn' : B < (n : ℝ) * ‖v‖ := (div_lt_iff₀ hp).mp hn
  have hb := hB (n • v) (hv n)
  simp only [← Nat.cast_smul_eq_nsmul ℝ,norm_smul,Real.norm_natCast] at hb
  linarith

variable {G Q : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]

omit [IsTopologicalGroup G] [IsTopologicalGroup Q] in
lemma noCompactPowers_extension (π : G →* Q) (hπ : Continuous π)
    (hQ : NoCompactPowers Q)
    (hker : ∀ g ∈ π.ker, ∀ K : Set G, IsCompact K → (∀ n : ℕ, g^n ∈ K) → g = 1) :
    NoCompactPowers G := by
  intro g K hK hg
  have hp : π g = 1 := hQ (π g) (π '' K) (hK.image hπ) (fun n =>
    ⟨g^n,hg n,map_pow π g n⟩)
  exact hker g hp K hK hg

omit [TopologicalSpace G] [IsTopologicalGroup G] in
lemma conjugate_pow_of_central_commutator (x g : G)
    (hc : x*g*x⁻¹*g⁻¹ ∈ Subgroup.center G) (n : ℕ) :
    x^n*g*(x^n)⁻¹*g⁻¹ = (x*g*x⁻¹*g⁻¹)^n := by
  let c := x*g*x⁻¹*g⁻¹
  have hxg : x*g = c*g*x := by dsimp [c]; group
  have hxc : Commute x c := Subgroup.mem_center_iff.mp hc x
  have he : ∀ n : ℕ, x^n*g = c^n*g*x^n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc
        x^(n+1)*g = x*(x^n*g) := by rw [pow_succ']; group
        _ = x*(c^n*g*x^n) := by rw [ih]
        _ = c^n*(x*g)*x^n := by rw [← mul_assoc,← mul_assoc,hxc.pow_right n |>.eq]; group
        _ = c^n*(c*g*x)*x^n := by rw [hxg]
        _ = c^(n+1)*g*x^(n+1) := by rw [pow_succ,pow_succ']; group
  change x^n*g*(x^n)⁻¹*g⁻¹ = c^n
  rw [he n]
  group

omit [IsTopologicalGroup Q] in
lemma compactConjugacy_extension (π : G →* Q) (hπ : Continuous π) (hπs : Surjective π)
    (hQ : CompactConjugacyCentral Q) (hC : π.ker ≤ Subgroup.center G)
    (hker : ∀ g ∈ π.ker, ∀ K : Set G, IsCompact K → (∀ n : ℕ, g^n ∈ K) → g = 1) :
    CompactConjugacyCentral G := by
  intro g K hK hg
  have hp : π g ∈ Subgroup.center Q := by
    apply hQ (π g) (π '' K) (hK.image hπ)
    intro y
    obtain ⟨x,rfl⟩ := hπs y
    exact ⟨x*g*x⁻¹,hg x,by simp⟩
  apply Subgroup.mem_center_iff.mpr
  intro x
  have hc : x*g*x⁻¹*g⁻¹ ∈ π.ker := by
    change π (x*g*x⁻¹*g⁻¹) = 1
    simp only [map_mul,map_inv]
    rw [Subgroup.mem_center_iff.mp hp (π x)]
    group
  have hz : x*g*x⁻¹*g⁻¹ = 1 := by
    apply hker _ hc ((fun y : G => y*g⁻¹) '' K) (hK.image (continuous_id.mul continuous_const))
    intro n
    refine ⟨x^n*g*(x^n)⁻¹,hg (x^n),?_⟩
    exact conjugate_pow_of_central_commutator x g (hC hc) n
  have := congrArg (fun y : G => y*g*x) hz
  simpa only [one_mul,mul_assoc,inv_mul_cancel_left,mul_inv_cancel_left,inv_mul_cancel,mul_one] using this

end RawCompactNilpotent

namespace RawCompactNilpotent
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

 

theorem centralizer_cocompact_le_center (Γ : Subgroup G) [CompactSpace (G ⧸ Γ)]
    (hG : CompactConjugacyCentral G) (g : G)
    (hg : ∀ γ ∈ Γ, γ*g = g*γ) : g ∈ Subgroup.center G := by
  let q : G ⧸ Γ → G := Quotient.lift (fun x : G => x*g*x⁻¹) (by
    intro x y h
    have hc := hg (x⁻¹*y) (QuotientGroup.leftRel_apply.mp h)
    have he := congrArg (fun z : G => x*z*y⁻¹) hc
    have he' : y*g*y⁻¹ = x*g*x⁻¹ := by
      calc
        y*g*y⁻¹ = x*((x⁻¹*y)*g)*y⁻¹ := by group
        _ = x*(g*(x⁻¹*y))*y⁻¹ := he
        _ = x*g*x⁻¹ := by group
    exact he'.symm)
  have hq : Continuous q := by
    apply (QuotientGroup.isQuotientMap_mk Γ).continuous_iff.mpr
    exact (continuous_id.mul continuous_const).mul continuous_inv
  apply hG g (Set.range q) (isCompact_range hq)
  intro x
  exact ⟨QuotientGroup.mk x,rfl⟩

end RawCompactNilpotent

namespace RawCompactNilpotent
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

omit [IsTopologicalGroup G] in
lemma noCompactPowers_vector_subgroup (S : Subgroup G) (hS : IsClosed (S : Set G))
    (H : V ≃ₜ S) (h0 : H 0 = 1) (ha : ∀ v w, H (v+w) = H v * H w) :
    ∀ g ∈ S, ∀ K : Set G, IsCompact K → (∀ n : ℕ, g^n ∈ K) → g = 1 := by
  have hzero : H.symm 1 = 0 := by rw [← h0,H.symm_apply_apply]
  have hmul : ∀ a b : S, H.symm (a*b) = H.symm a + H.symm b := by
    intro a b
    apply H.injective
    rw [H.apply_symm_apply,ha,H.apply_symm_apply,H.apply_symm_apply]
  have hp : ∀ (g : S) (n : ℕ), H.symm (g^n) = n • H.symm g := by
    intro g n
    induction n with
    | zero => simp [hzero]
    | succ n ih => rw [pow_succ,hmul,ih,add_nsmul,one_nsmul]
  intro g hg K hK hpow
  let sg : S := ⟨g,hg⟩
  have hcompact : IsCompact (H.symm '' ((Subtype.val : S → G) ⁻¹' K)) :=
    (hS.isClosedEmbedding_subtypeVal.isCompact_preimage hK).image H.symm.continuous
  have hn : ∀ n : ℕ, n • H.symm sg ∈ H.symm '' ((Subtype.val : S → G) ⁻¹' K) := by
    intro n
    exact ⟨sg^n,hpow n,hp sg n⟩
  have hz := eq_zero_of_compact_nsmul (H.symm sg) _ hcompact hn
  have he : sg = 1 := by
    rw [← H.apply_symm_apply sg,hz,h0]
  exact congrArg Subtype.val he

end RawCompactNilpotent

namespace RawPowerExtension

variable {G Q : Type*} [Group G] [Group Q]

lemma pow_injective_extension (π : G →* Q)
    (hQ : ∀ n : ℕ, n ≠ 0 → Injective (fun x : Q => x^n))
    (hC : π.ker ≤ Subgroup.center G)
    (hk : ∀ c ∈ π.ker, ∀ n : ℕ, n ≠ 0 → c^n = 1 → c = 1) :
    ∀ n : ℕ, n ≠ 0 → Injective (fun x : G => x^n) := by
  intro n hn x y hxy
  change x^n = y^n at hxy
  have hπxy : π x = π y := hQ n hn (by simpa only [← map_pow] using congrArg π hxy)
  let c := x⁻¹*y
  have hc : c ∈ π.ker := by simp only [MonoidHom.mem_ker,c,map_mul,map_inv,hπxy,inv_mul_cancel]
  have he : y = x*c := by dsimp [c]; group
  have hcc : Commute x c := Subgroup.mem_center_iff.mp (hC hc) x
  have hcPow : c^n = 1 := by
    rw [he,hcc.mul_pow] at hxy
    exact (mul_eq_left.mp hxy.symm)
  have hc1 := hk c hc n hn hcPow
  rw [he,hc1,mul_one]

lemma no_torsion_of_no_compact_powers [TopologicalSpace G]
    (hp : ∀ g : G, ∀ K : Set G, IsCompact K → (∀ n : ℕ, g^n ∈ K) → g = 1)
    (g : G) (n : ℕ) (hn : n ≠ 0) (he : g^n = 1) : g = 1 := by
  apply hp g (Set.range (fun i : Fin n => g^i.val)) (Set.finite_range _).isCompact
  intro m
  exact ⟨⟨m % n,Nat.mod_lt _ (Nat.pos_of_ne_zero hn)⟩,(pow_eq_pow_mod m he).symm⟩

end RawPowerExtension

namespace RawPowerExtension
variable {G : Type*} [Group G] [TopologicalSpace G] [T2Space G]

lemma real_oneparameter_unique (hp : ∀ n : ℕ, n ≠ 0 → Injective (fun g : G => g^n))
    (φ ψ : Multiplicative ℝ →* G) (hφ : Continuous φ) (hψ : Continuous ψ)
    (he : φ (Multiplicative.ofAdd 1) = ψ (Multiplicative.ofAdd 1)) : φ = ψ := by
  have hq (q : ℚ) : φ (Multiplicative.ofAdd (q : ℝ)) = ψ (Multiplicative.ofAdd (q : ℝ)) := by
    apply hp q.den q.den_nz
    have hqr : (q.den : ℝ) * (q : ℝ) = (q.num : ℝ) := by exact_mod_cast q.den_mul_eq_num
    have hmul : (Multiplicative.ofAdd (q : ℝ))^q.den = (Multiplicative.ofAdd (1 : ℝ))^q.num := by
      change Multiplicative.ofAdd (q.den • (q : ℝ)) = Multiplicative.ofAdd (q.num • (1 : ℝ))
      rw [nsmul_eq_mul,zsmul_eq_mul,mul_one,hqr]
    change φ (Multiplicative.ofAdd (q : ℝ))^q.den = ψ (Multiplicative.ofAdd (q : ℝ))^q.den
    rw [← map_pow φ,← map_pow ψ,hmul,map_zpow φ,map_zpow ψ,he]
  have hreal : (fun t : ℝ => φ (Multiplicative.ofAdd t)) = fun t : ℝ => ψ (Multiplicative.ofAdd t) :=
    Rat.denseRange_cast.equalizer hφ hψ (funext hq)
  exact MonoidHom.ext (fun t => congrFun hreal t.toAdd)
end RawPowerExtension
end

end OAI
