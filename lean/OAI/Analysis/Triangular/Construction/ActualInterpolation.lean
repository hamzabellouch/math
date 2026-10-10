import OAI.Analysis.Triangular.Construction.FiniteInterpolation

namespace OAI

noncomputable section
open scoped BigOperators lp
open Complex Matrix
namespace AtomicTriangular.Construction
lemma otherSide_zero : otherSide 0=1 := rfl
lemma otherSide_one : otherSide 1=0 := rfl
def actualJ (side : Fin 2) (z : ℝ) (hz : 0<z) (hzB : z≤Z) : ℝ → ℝ :=
  pairJ (actualInput side z hz hzB) (actualInput (otherSide side) z hz hzB)
def gaussianG (z s : ℝ) : ℝ := Q 1*z*Real.exp ((1-s)/z)
lemma gaussianG_deriv {z : ℝ} (hz : 0<z) (s : ℝ) :
    HasDerivAt (gaussianG z) (-Q 1*Real.exp ((1-s)/z)) s := by
  have hh := ((((hasDerivAt_const s (1:ℝ)).sub (hasDerivAt_id s)).div_const z).exp.const_mul (Q 1*z))
  convert hh using 1 <;> first | rfl | (simp only [Pi.sub_apply,id_eq]; field_simp; ring)
lemma negativeJet_gaussian {z : ℝ} (hz : 0<z) (v : ℝ) (n : ℤ) (d : Fin 2) :
    (negativeJet v n d (gaussianG z n:ℂ) ((deriv (gaussianG z) (n:ℝ):ℝ):ℂ)).re = -gaussianTarget v z n d := by
  rw [negativeJet_re,(gaussianG_deriv hz n).deriv]
  simp only [ofReal_re,gaussianG,gaussianTarget,Real.exp_add]
  split_ifs <;> ring
lemma negativeJet_injective (v : ℝ) (n : Node) (a b c d : ℂ)
    (h0 : (negativeJet v n.val 0 a b).re=(negativeJet v n.val 0 c d).re)
    (h1 : (negativeJet v n.val 1 a b).re=(negativeJet v n.val 1 c d).re) :
    a.re=c.re ∧ b.re=d.re := by
  simp only [negativeJet_re,Fin.val_zero,Fin.val_one,Nat.one_ne_zero,↓reduceIte] at h0 h1
  have hp : Real.exp (Real.pi*(v-h)*n.val)/Q n.val≠0 := div_ne_zero (Real.exp_ne_zero _) (Q_node_ne n)
  have ha : a.re=c.re := by
    have hh := mul_left_cancel₀ hp h0
    linarith
  have hb := mul_left_cancel₀ hp h1
  constructor
  · exact ha
  · rw [ha] at hb
    linarith
lemma finiteNode_surj {n : ℤ} (hn : n∈FiniteNodes) : ∃ i : Fin 10,finiteNode i=n := by
  have hall : ∀ n∈FiniteNodes,∃ i : Fin 10,finiteNode i=n := by decide +kernel
  exact hall n hn
lemma rowNode_cover (n : Node) (hn : n.val∈FiniteNodes) (d : Fin 2) :
    ∃ i : Fin 20,rowNode i=n ∧ rowDerivative i=d := by
  obtain ⟨j,hj⟩ := finiteNode_surj hn
  refine ⟨⟨2*j.val+d.val,by omega⟩,?_,?_⟩
  · apply Subtype.ext
    change finiteNode ⟨(2*j.val+d.val)/2,by omega⟩=n.val
    convert hj using 1
    congr 1
    apply Fin.ext
    dsimp
    omega
  · apply Fin.ext
    change (2*j.val+d.val)%2=d.val
    omega
lemma actual_node_negative {z : ℝ} (hz : 0<z) (hzB : z≤Z) (n : Node) :
    ∃ v : ℝ,∀ d : Fin 2,
      (negativeJet v n.val d
        (pairJJet (actualInput 0 z hz hzB) (actualInput 1 z hz hzB) 0 n.val)
        (pairJJet (actualInput 0 z hz hzB) (actualInput 1 z hz hzB) 1 n.val)).re= -gaussianTarget v z n.val d ∧
      (negativeJet v n.val d
        (pairJJet (actualInput 1 z hz hzB) (actualInput 0 z hz hzB) 0 n.val)
        (pairJJet (actualInput 1 z hz hzB) (actualInput 0 z hz hzB) 1 n.val)).re=0 := by
  by_cases hn : n.val∈FiniteNodes
  · refine ⟨H,?_⟩
    intro d
    obtain ⟨i,hi,hd⟩ := rowNode_cover n hn d
    have hh := actual_finite_negative hz hzB i
    simpa only [hi,hd] using hh
  · refine ⟨h,?_⟩
    intro d
    exact actual_tail_negative hz hzB (⟨n,hn⟩,d)
lemma actual_interpolation {z : ℝ} (hz : 0<z) (hzB : z≤Z) (n : Node) :
    actualJ 0 z hz hzB n.val=gaussianG z n.val ∧ deriv (actualJ 0 z hz hzB) n.val=deriv (gaussianG z) n.val ∧
    actualJ 1 z hz hzB n.val=0 ∧ deriv (actualJ 1 z hz hzB) n.val=0 := by
  obtain ⟨v,hv⟩ := actual_node_negative hz hzB n
  have h0 := negativeJet_injective v n
    (pairJJet (actualInput 0 z hz hzB) (actualInput 1 z hz hzB) 0 n.val)
    (pairJJet (actualInput 0 z hz hzB) (actualInput 1 z hz hzB) 1 n.val)
    (gaussianG z n.val:ℂ) ((deriv (gaussianG z) (n.val:ℝ):ℝ):ℂ)
    ((hv 0).1.trans (negativeJet_gaussian hz v n.val 0).symm)
    ((hv 1).1.trans (negativeJet_gaussian hz v n.val 1).symm)
  have hn0 (d : Fin 2) : negativeJet v n.val d 0 0=0 := by simp [negativeJet]
  have h1 := negativeJet_injective v n
    (pairJJet (actualInput 1 z hz hzB) (actualInput 0 z hz hzB) 0 n.val)
    (pairJJet (actualInput 1 z hz hzB) (actualInput 0 z hz hzB) 1 n.val) 0 0
    (by simpa only [hn0,zero_re] using (hv 0).2) (by simpa only [hn0,zero_re] using (hv 1).2)
  have hd0 := ((hasDerivAt_pairJJet (actualInput 0 z hz hzB) (actualInput 1 z hz hzB) 0 n.val).real_of_complex).deriv
  have hd1 := ((hasDerivAt_pairJJet (actualInput 1 z hz hzB) (actualInput 0 z hz hzB) 0 n.val).real_of_complex).deriv
  change deriv (actualJ 0 z hz hzB) n.val=(pairJJet _ _ 1 n.val).re at hd0
  change deriv (actualJ 1 z hz hzB) n.val=(pairJJet _ _ 1 n.val).re at hd1
  exact ⟨h0.1,hd0.trans h0.2,h1.1,hd1.trans h1.2⟩
end AtomicTriangular.Construction
end

end OAI
