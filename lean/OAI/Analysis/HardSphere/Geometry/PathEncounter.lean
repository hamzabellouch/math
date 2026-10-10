import Mathlib
import OAI.Analysis.HardSphere.Geometry.CandidateConstant
import OAI.Analysis.HardSphere.Geometry.EndpointDanger

namespace OAI

noncomputable section
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped ENNReal NNReal
open scoped ENNReal
namespace HardSphere.Lattice

lemma accepted_charge_environment_bound {K : ℕ} [NeZero K] (R : ℕ)
    (μ : PMF (Finset (DiscreteTorus K))) (p κ C N : ℝ)
    (hp : 0≤p) (hκ : 0≤κ) (hbad : JointBadLaw μ (ENNReal.ofReal p))
    (Γ Γ' : Finset (DiscreteTorus K)) (E : Finset (DiscreteTorus K) → Prop)
    (J : Finset (DiscreteTorus K) → ℝ)
    (hJ : ∀ B, E B → J B≤N+C*∑ F∈badComponents (torusRangeGraph K (R+2)) B,
      if torusContact (R+2) F Γ ∧ torusContact (R+2) F Γ' then (F.card:ℝ) else 0) :
    (∑' B, μ B*(if E B then ENNReal.ofReal (Real.exp (κ*J B)) else 0))≤
      ENNReal.ofReal (Real.exp (κ*N+∑ F∈candidateSets (torusRangeGraph K (R+2)),
        if torusContact (R+2) F Γ ∧ torusContact (R+2) F Γ' then (p*Real.exp (κ*C))^F.card else 0)) := by
  have henv := badComponents_exponential_bound (torusRangeGraph K (R+2)) μ p (κ*C) hp hbad
    (fun F ↦ torusContact (R+2) F Γ ∧ torusContact (R+2) F Γ')
  let S (B : Finset (DiscreteTorus K)) : ℝ := ∑ F∈badComponents (torusRangeGraph K (R+2)) B,
    if torusContact (R+2) F Γ ∧ torusContact (R+2) F Γ' then (F.card:ℝ) else 0
  calc
    _ ≤ ∑' B, μ B*ENNReal.ofReal (Real.exp (κ*N+κ*C*S B)) := by
      apply ENNReal.tsum_le_tsum
      intro B
      apply mul_le_mul' le_rfl
      by_cases hB : E B
      · rw [ite_eq_left hB]
        apply ENNReal.ofReal_le_ofReal
        apply Real.exp_le_exp.mpr
        calc
          κ*J B ≤ κ*(N+C*S B) := mul_le_mul_of_nonneg_left (hJ B hB) hκ
          _ = _ := by ring
      · rw [ite_eq_right hB]; exact zero_le
    _ = ENNReal.ofReal (Real.exp (κ*N)) *
        ∑' B, μ B*ENNReal.ofReal (Real.exp (κ*C*S B)) := by
      rw [← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro B
      rw [Real.exp_add,ENNReal.ofReal_mul (Real.exp_pos _).le]
      ring
    _ ≤ ENNReal.ofReal (Real.exp (κ*N))*
        ENNReal.ofReal (Real.exp (∑ F∈candidateSets (torusRangeGraph K (R+2)),
          if torusContact (R+2) F Γ ∧ torusContact (R+2) F Γ' then (p*Real.exp (κ*C))^F.card else 0)) := by
      apply mul_le_mul' le_rfl
      change (∑' B, μ B * ENNReal.ofReal (Real.exp ((κ*C) * S B))) ≤ _
      convert henv using 1
      · congr 1
        funext B
        congr 3
        congr 1
        dsimp only [S]
        apply Finset.sum_congr rfl
        intro F hF
        split_ifs <;> rfl
      · congr 2
        apply Finset.sum_congr rfl
        intro F hF
        split_ifs <;> rfl
    _ = _ := by rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,← Real.exp_add]

def pathEncounter {K : ℕ} (R : ℕ) {B : Finset (DiscreteTorus K)} {x y : DiscreteTorus K}
    (p q : SimpleGoodPath B x y) : ℕ :=
  (encounterSet (torusNear K R) p.val.support.toFinset q.val.support.toFinset).card

def pathKernelMoment {K : ℕ} (R : ℕ) (κ : ℝ) {B : Finset (DiscreteTorus K)} {x y : DiscreteTorus K}
    (ν : PMF (SimpleGoodPath B x y)) : ℝ≥0∞ :=
  ∑' p, ν p*∑' q, ν q*ENNReal.ofReal (Real.exp (κ*(pathEncounter R p q:ℝ)))

lemma goodPathKernel_moment_noises {K m n : ℕ} [NeZero K] (hK : 2<K) (R : ℕ)
    (hn : 0<n) (ht : n/2≤3^m) (v : Vertex) (Δ₂ Δ₃ : ℤ)
    (hΔ₂ : |Δ₂|≤2*n) (hΔ₃ : |Δ₃|≤2*n) (B : Finset (DiscreteTorus K))
    (hB : acceptedEnvironment (R+2) B v (v+![(n:ℤ),Δ₂,Δ₃])) (κ : ℝ) :
    pathKernelMoment R κ (goodPathKernel hK R hn ht v Δ₂ Δ₃ hΔ₂ hΔ₃ B hB)=
      ∑' w, fourLaw m w*ENNReal.ofReal (Real.exp (κ*(pathEncounter R
        (detourSample hK R hn ht v Δ₂ Δ₃ hΔ₂ hΔ₃ B hB (firstPathNoise w))
        (detourSample hK R hn ht v Δ₂ Δ₃ hΔ₂ hΔ₃ B hB (secondPathNoise w)):ℝ))) := by
  unfold pathKernelMoment goodPathKernel
  simp_rw [pmf_map_expectation]
  exact pair_expectation_transpose m _

lemma detourSample_charge {K m n : ℕ} [NeZero K] (hK : 2<K) (R : ℕ)
    (hn : 0<n) (ht : n/2≤3^m) (v : Vertex) (Δ₂ Δ₃ : ℤ)
    (hΔ₂ : |Δ₂|≤2*n) (hΔ₃ : |Δ₃|≤2*n) (B : Finset (DiscreteTorus K))
    (hB : acceptedEnvironment (R+2) B v (v+![(n:ℤ),Δ₂,Δ₃])) (w : FourNoise m) :
    let Γ := (nominalCover (nominalVertices m n v Δ₂ Δ₃ (firstPathNoise w))).image (torusProjection K)
    let Γ' := (nominalCover (nominalVertices m n v Δ₂ Δ₃ (secondPathNoise w))).image (torusProjection K)
    (pathEncounter R
      (detourSample hK R hn ht v Δ₂ Δ₃ hΔ₂ hΔ₃ B hB (firstPathNoise w))
      (detourSample hK R hn ht v Δ₂ Δ₃ hΔ₂ hΔ₃ B hB (secondPathNoise w)):ℝ) ≤
    ((encounterSet (torusNear K R) Γ Γ').card:ℝ)+
      (encounterConstant R:ℝ)*∑ F∈badComponents (torusRangeGraph K (R+2)) B,
        if torusContact (R+2) F Γ ∧ torusContact (R+2) F Γ' then (F.card:ℝ) else 0 := by
  dsimp only
  let u := detourSample hK R hn ht v Δ₂ Δ₃ hΔ₂ hΔ₃ B hB (firstPathNoise w)
  let u' := detourSample hK R hn ht v Δ₂ Δ₃ hΔ₂ hΔ₃ B hB (secondPathNoise w)
  let Γ := (nominalCover (nominalVertices m n v Δ₂ Δ₃ (firstPathNoise w))).image (torusProjection K)
  let Γ' := (nominalCover (nominalVertices m n v Δ₂ Δ₃ (secondPathNoise w))).image (torusProjection K)
  have h := torus_detour_charge R B Γ Γ' u.val.support.toFinset u'.val.support.toFinset
    (fun x hx ↦ ⟨u.property.2 x (List.mem_toFinset.mp hx),
      detourSample_attachment hK R hn ht v Δ₂ Δ₃ hΔ₂ hΔ₃ B hB _ x (List.mem_toFinset.mp hx)⟩)
    (fun x hx ↦ ⟨u'.property.2 x (List.mem_toFinset.mp hx),
      detourSample_attachment hK R hn ht v Δ₂ Δ₃ hΔ₂ hΔ₃ B hB _ x (List.mem_toFinset.mp hx)⟩)
  have h' := h.trans (Nat.add_le_add_left
    (Nat.mul_le_mul_right _ (encounterConstant_detour R)) _)
  have hreal := (Nat.cast_le (α:=ℝ)).mpr h'
  simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_sum,Finset.sum_filter,Nat.cast_ite,Nat.cast_zero,pathEncounter,u,u',Γ,Γ'] using hreal

theorem good_kernel_average_le_folded {K m n : ℕ} [NeZero K] (hK : 2<K) (R : ℕ)
    (hn : 0<n) (hnK : 2*n≤K) (ht : n/2≤3^m) (v : Vertex) (Δ₂ Δ₃ : ℤ)
    (hΔ₂ : |Δ₂|≤2*n) (hΔ₃ : |Δ₃|≤2*n) (μ : PMF (Finset (DiscreteTorus K)))
    (p κ : ℝ) (hp : 0≤p) (hκ : 0≤κ) (hbad : JointBadLaw μ (ENNReal.ofReal p))
    (hqt : (candidateConstant (R+2):ℝ)*(p*Real.exp (κ*(encounterConstant R:ℝ)))<1) :
    (∑' B, μ B*(if hB : acceptedEnvironment (R+2) B v (v+![(n:ℤ),Δ₂,Δ₃]) then
      pathKernelMoment R κ (goodPathKernel hK R hn ht v Δ₂ Δ₃ hΔ₂ hΔ₃ B hB) else 0))≤
    ∑' w, fourLaw m w*ENNReal.ofReal (Real.exp
      (∑ j∈Finset.range (n+1), radiusPotential
        (geometricRadiusWeights (candidateConstant (R+2)) (4*(R+6))
          (ENNReal.ofReal ((encounterConstant R:ℝ)*κ))
          (ENNReal.ofReal ((candidateConstant (R+2):ℝ)*p*Real.exp (κ*(encounterConstant R:ℝ)))))
        (differenceAt m (min j (n-j)) w))) := by
  let E (B : Finset (DiscreteTorus K)) := acceptedEnvironment (R+2) B v (v+![(n:ℤ),Δ₂,Δ₃])
  let J (B : Finset (DiscreteTorus K)) (w : FourNoise m) : ℝ := if hB : E B then
    (pathEncounter R
      (detourSample hK R hn ht v Δ₂ Δ₃ hΔ₂ hΔ₃ B hB (firstPathNoise w))
      (detourSample hK R hn ht v Δ₂ Δ₃ hΔ₂ hΔ₃ B hB (secondPathNoise w)):ℝ) else 0
  let f (B : Finset (DiscreteTorus K)) (w : FourNoise m) : ℝ≥0∞ :=
    if E B then ENNReal.ofReal (Real.exp (κ*J B w)) else 0
  have hrep (B : Finset (DiscreteTorus K)) :
      (if hB : E B then pathKernelMoment R κ (goodPathKernel hK R hn ht v Δ₂ Δ₃ hΔ₂ hΔ₃ B hB) else 0)=
      ∑' w, fourLaw m w*f B w := by
    by_cases hB : E B
    · simp only [dite_eq_left hB,f,ite_eq_left hB,J]
      exact goodPathKernel_moment_noises hK R hn ht v Δ₂ Δ₃ hΔ₂ hΔ₃ B hB κ
    · simp only [dite_eq_right hB,f,ite_eq_right hB,mul_zero,tsum_zero]
  have henv (w : FourNoise m) :
      (∑' B, μ B*f B w)≤ENNReal.ofReal (Real.exp
        (∑ j∈Finset.range (n+1), radiusPotential
          (geometricRadiusWeights (candidateConstant (R+2)) (4*(R+6))
            (ENNReal.ofReal ((encounterConstant R:ℝ)*κ))
            (ENNReal.ofReal ((candidateConstant (R+2):ℝ)*p*Real.exp (κ*(encounterConstant R:ℝ)))))
          (differenceAt m (min j (n-j)) w))) := by
    let Γ := (nominalCover (nominalVertices m n v Δ₂ Δ₃ (firstPathNoise w))).image (torusProjection K)
    let Γ' := (nominalCover (nominalVertices m n v Δ₂ Δ₃ (secondPathNoise w))).image (torusProjection K)
    have hcharge : ∀ B, E B → J B w≤((encounterSet (torusNear K R) Γ Γ').card:ℝ)+
        (encounterConstant R:ℝ)*∑ F∈badComponents (torusRangeGraph K (R+2)) B,
          if torusContact (R+2) F Γ ∧ torusContact (R+2) F Γ' then (F.card:ℝ) else 0 := by
      intro B hB
      simp only [J,dite_eq_left hB]
      exact detourSample_charge hK R hn ht v Δ₂ Δ₃ hΔ₂ hΔ₃ B hB w
    have hc := accepted_charge_environment_bound R μ p κ (encounterConstant R)
      ((encounterSet (torusNear K R) Γ Γ').card:ℝ) hp hκ hbad Γ Γ' E (fun B ↦ J B w) hcharge
    refine hc.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_))
    have hb := nominal_potential_bound R hn hnK ht v Δ₂ Δ₃ hΔ₂ hΔ₃ w κ
      (p*Real.exp (κ*(encounterConstant R:ℝ))) hκ (mul_nonneg hp (Real.exp_pos _).le) hqt
    simpa only [mul_assoc] using hb
  calc
    _ = ∑' B, μ B*∑' w, fourLaw m w*f B w := by
      apply tsum_congr
      intro B
      rw [hrep B]
    _ = ∑' w, fourLaw m w*∑' B, μ B*f B w := by
      simp_rw [← ENNReal.tsum_mul_left]
      rw [ENNReal.tsum_comm]
      apply tsum_congr
      intro w
      apply tsum_congr
      intro B
      ring
    _ ≤ _ := ENNReal.tsum_le_tsum fun w ↦ mul_le_mul' le_rfl (henv w)

theorem good_kernel_uniform_constants (R : ℕ) :
    ∃ p₀ κ : ℝ, 0<p₀ ∧ 0<κ ∧ ∃ K₀ : ℕ, ∀ K : ℕ, K₀≤K → ∀ _ : NeZero K,
      ∀ μ : PMF (Finset (DiscreteTorus K)), ∀ p : ℝ, 0≤p → p≤p₀ →
      JointBadLaw μ (ENNReal.ofReal p) →
      ∀ n : ℕ, ∀ hn : 0<n, 2*n≤K → ∀ m : ℕ, ∀ ht : n/2≤3^m,
      ∀ v : Vertex, ∀ Δ₂ Δ₃ : ℤ, ∀ hΔ₂ : |Δ₂|≤2*n, ∀ hΔ₃ : |Δ₃|≤2*n,
      ∃ hK : 2<K,
        (1/2:ℝ≥0∞)≤(∑' B, if acceptedEnvironment (R+2) B v (v+![(n:ℤ),Δ₂,Δ₃]) then μ B else 0) ∧
        (∑' B, μ B*(if hB : acceptedEnvironment (R+2) B v (v+![(n:ℤ),Δ₂,Δ₃]) then
          pathKernelMoment R κ (goodPathKernel hK R hn ht v Δ₂ Δ₃ hΔ₂ hΔ₃ B hB) else 0))≤2 := by
  let A := candidateConstant (R+2)
  let C := encounterConstant R
  obtain ⟨κ,q₀,hκ,hq₀,hmoment⟩ := geometric_folded_moment A (4*(R+6)) (C:ℝ) (Nat.cast_nonneg _)
  obtain ⟨p₁,hp₁,K₁,haccept⟩ := acceptedEnvironment_mass (R+2) (by omega)
  have hA : 0<(A:ℝ) := by
    have hAn : 0<A := by dsimp [A,candidateConstant]; positivity
    exact_mod_cast hAn
  let p₂ := 1/(2*(A:ℝ)*Real.exp (κ*(C:ℝ)))
  have hp₂ : 0<p₂ := by dsimp [p₂]; positivity
  refine ⟨min p₁ (min q₀ p₂),κ,lt_min hp₁ (lt_min hq₀ hp₂),hκ,max K₁ 3,?_⟩
  intro K hK inst μ p hp hpp hbad n hn hnK m ht v Δ₂ Δ₃ hΔ₂ hΔ₃
  have hK2 : 2<K := by have := (le_max_right K₁ 3).trans hK; omega
  have hp₁' : p≤p₁ := hpp.trans (min_le_left _ _)
  have hpq : p≤q₀ := (hpp.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hp₂' : p≤p₂ := (hpp.trans (min_le_right _ _)).trans (min_le_right _ _)
  have hqt : (A:ℝ)*(p*Real.exp (κ*(C:ℝ)))<1 := by
    have h := (le_div_iff₀ (show 0<2*(A:ℝ)*Real.exp (κ*(C:ℝ)) by positivity)).mp hp₂'
    nlinarith
  refine ⟨hK2,haccept K ((le_max_left _ _).trans hK) inst μ p hp hp₁' hbad v _,?_⟩
  refine (good_kernel_average_le_folded hK2 R hn hnK ht v Δ₂ Δ₃ hΔ₂ hΔ₃ μ p κ hp hκ.le hbad hqt).trans ?_
  exact hmoment p hp hpq m n ht

end HardSphere.Lattice

end

end OAI
