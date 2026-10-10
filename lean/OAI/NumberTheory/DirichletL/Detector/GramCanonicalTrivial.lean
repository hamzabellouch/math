import OAI.NumberTheory.DirichletL.Detector.GramCanonicalBlock

namespace OAI

noncomputable section
open scoped Classical SchwartzMap
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CompletedGauss RayFourExpansion ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem canonical_trivial_block (a b B : ℝ) (ha : 0<a) (hb : 0≤b) (hB : 0≤B) (A : ℕ) :
    ∃s : Finset (ℕ×ℕ),∃K : ℝ,0<K ∧
      ∀(W : ℝ→ℂ)(_hcompact : HasCompactSupport W),
      (Function.support W⊆Set.Icc a b)→(∀x,‖W x‖≤B)→
      ∀(U : SchwartzMap ℝ ℂ)(S : Finset Id)(hS : ∀p∈S,p.IsMaximal)(σ : RayRing)
      (C : SupportedIdeal)(k : GramFrequency)(d : O)(N T v : ℝ),0<N→0≤T→
      (1+T)^A*‖canonicalLatticeBlock S hS σ C k d W U v T N‖≤
        K*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(Ideal.absNorm C.val:ℝ)*N^2 := by
  obtain ⟨s,K,hK,hprofile⟩ := shellProfile_weighted_bound a b B ha hB A
  refine ⟨s,(1+128*b)^2*K,by positivity,?_⟩
  intro W hcompact hs hW U S hS σ C k d N T v hN hT
  let F:=shellLatticeColumns W hcompact N hN
  let G:=F
  have hF0 : ∀z∈F,z≠0 := shellLatticeColumns_nonzero W hcompact N hN a b ha hs
  have hG0 : ∀z∈G,z≠0 := hF0
  have hFN : ∀z∈F,‖eisEmbedding z‖^2≤b*N := shellLatticeColumns_norm W hcompact N hN a b hs
  have hGN : ∀z∈G,‖eisEmbedding z‖^2≤b*N := hFN
  unfold canonicalLatticeBlock
  rw [shell_lattice_tsum W hcompact N hN U v T (fun n m=>canonicalJoint S hS σ C k (d*n) (d*m))]
  have hcoef (n m : O) : ‖canonicalJoint S hS σ C k (d*n) (d*m)‖≤(Ideal.absNorm C.val:ℝ) :=
    canonicalJoint_norm S hS σ C k _ _
  have hpoint (n m : O) : (1+T)^A*‖canonicalJoint S hS σ C k (d*n) (d*m)*
      shellProfile W v U T (‖eisEmbedding n‖^2/N) (‖eisEmbedding m‖^2/N)‖≤
      (Ideal.absNorm C.val:ℝ)*(K*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) U) := by
    rw [norm_mul]
    calc
      _ = ‖canonicalJoint S hS σ C k (d*n) (d*m)‖*
          ((1+T)^A*‖shellProfile W v U T (‖eisEmbedding n‖^2/N) (‖eisEmbedding m‖^2/N)‖) := by ring
      _ ≤ _ := mul_le_mul (hcoef n m) (hprofile W hs hW U v T _ _ hT) (by positivity) (by positivity)
  have hcount := annular_pair_count F G b N hb hN.le hF0 hG0 hFN hGN
  calc
    _ ≤ (1+T)^A*(∑n∈F,∑m∈G,‖canonicalJoint S hS σ C k (d*n) (d*m)*
        shellProfile W v U T (‖eisEmbedding n‖^2/N) (‖eisEmbedding m‖^2/N)‖) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _=>norm_sum_le _ _)
    _ ≤ (F.card:ℝ)*G.card*((Ideal.absNorm C.val:ℝ)*(K*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) U)) := by
      simp_rw [Finset.mul_sum]
      calc
        _ ≤ ∑n∈F,∑m∈G,(Ideal.absNorm C.val:ℝ)*(K*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) U) :=
          Finset.sum_le_sum (fun n _=>Finset.sum_le_sum (fun m _=>hpoint n m))
        _ = _ := by simp;ring
    _ ≤ ((128*b)^2*N^2)*((Ideal.absNorm C.val:ℝ)*(K*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) U)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      simpa only [Finset.card_product,Nat.cast_mul] using hcount
    _ ≤ _ := by
      have hb' : (128*b)^2≤(1+128*b)^2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right hb' (show 0≤N^2*((Ideal.absNorm C.val:ℝ)*
        (K*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) U)) by positivity)]

end SevenEighths.ProbeGramCommon
end

end OAI
