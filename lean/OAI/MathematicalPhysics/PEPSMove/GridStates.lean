import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator MatrixOrder
open Matrix

noncomputable section
open scoped BigOperators ComplexOrder
namespace PolynomialPEPS.PhysicalMove

abbrev Vertex (L : ℕ) := Fin L × Fin L

def ForwardAdjacent {L : ℕ} (v w : Vertex L) : Prop :=
  (v.1.val + 1 = w.1.val ∧ v.2 = w.2) ∨
  (v.1 = w.1 ∧ v.2.val + 1 = w.2.val)

abbrev Edge (L : ℕ) := {e : Vertex L × Vertex L // ForwardAdjacent e.1 e.2}

instance edgeFintype (L : ℕ) : Fintype (Edge L) := Fintype.ofFinite _

def Incident {L : ℕ} (v : Vertex L) (e : Edge L) : Prop :=
  v = e.val.1 ∨ v = e.val.2

abbrev IncidentEdge {L : ℕ} (v : Vertex L) := {e : Edge L // Incident v e}
instance incidentFintype {L : ℕ} (v : Vertex L) : Fintype (IncidentEdge v) :=
  Fintype.ofFinite _

abbrev Configuration (L q : ℕ) := Vertex L → Fin q
abbrev State (L q : ℕ) := EuclideanSpace ℂ (Configuration L q)
abbrev Operator (L q : ℕ) := Matrix (Configuration L q) (Configuration L q) ℂ
abbrev RegionConfiguration {L : ℕ} (q : ℕ) (S : Finset (Vertex L)) :=
  {v : Vertex L // v ∈ S} → Fin q

                                                                                
def liftLocal {L q : ℕ} (S : Finset (Vertex L))
    (a : Matrix (RegionConfiguration q S) (RegionConfiguration q S) ℂ) :
    Operator L q := fun x y =>
  if ∀ v, v ∉ S → x v = y v then
    a (fun v => x v.val) (fun v => y v.val)
  else 0

def SupportedOn {L q : ℕ} (a : Operator L q) (S : Finset (Vertex L)) : Prop :=
  ∃ aS : Matrix (RegionConfiguration q S) (RegionConfiguration q S) ℂ,
    a = liftLocal S aS

def EdgeSites {L : ℕ} (e : Edge L) : Finset (Vertex L) := {e.val.1, e.val.2}

def Hamiltonian {L q : ℕ} (hv : Vertex L → Operator L q)
    (he : Edge L → Operator L q) : Operator L q :=
  (∑ v, hv v) + ∑ e, he e

def asMap {L q : ℕ} (a : Operator L q) : State L q →L[ℂ] State L q :=
  Matrix.toEuclideanCLM (n := Configuration L q) (𝕜 := ℂ) a

def opNorm {L q : ℕ} (a : Operator L q) : ℝ := ‖asMap a‖

                                                                            
def IsGridHamiltonian {L q : ℕ} (J : ℝ)
    (hv : Vertex L → Operator L q) (he : Edge L → Operator L q) : Prop :=
  (∀ v, SupportedOn (hv v) {v} ∧ opNorm (hv v) ≤ J) ∧
  (∀ e, SupportedOn (he e) (EdgeSites e) ∧ opNorm (he e) ≤ J) ∧
  (Hamiltonian hv he).IsHermitian

def phase (θ : ℝ) : ℂ := Complex.exp ((θ : ℂ) * Complex.I)

                                                                                
def UniqueGround {L q : ℕ} (H : Operator L q) (Ω : State L q) (E₀ : ℝ) : Prop :=
  ‖Ω‖ = 1 ∧
  asMap H Ω = (E₀ : ℂ) • Ω ∧
  (∀ ψ : State L q,
    E₀ * ‖ψ‖ ^ 2 ≤ (inner ℂ ψ (asMap H ψ)).re) ∧
  (∀ ψ : State L q, ‖ψ‖ = 1 →
    asMap H ψ = (E₀ : ℂ) • ψ →
    ∃ θ : ℝ, ψ = phase θ • Ω)

                                                                         
def FullSystemGap {L q : ℕ} (H : Operator L q) (Ω : State L q)
    (E₀ Δ : ℝ) : Prop :=
  ∀ ψ : State L q,
    Δ * (‖ψ‖ ^ 2 - ‖inner ℂ Ω ψ‖ ^ 2) ≤
      (inner ℂ ψ (asMap H ψ)).re - E₀ * ‖ψ‖ ^ 2

                                                                             
abbrev LocalTensor {L : ℕ} (q : ℕ) (D : Edge L → ℕ) (v : Vertex L) :=
  Fin q → ((e : IncidentEdge v) → Fin (D e.val)) → ℂ

                                                                         
                                              
def contractPEPS {L q : ℕ} (D : Edge L → ℕ)
    (A : (v : Vertex L) → LocalTensor q D v) : State L q :=
  WithLp.toLp 2 (fun x => ∑ a : (e : Edge L) → Fin (D e),
    ∏ v : Vertex L, A v (x v) (fun e => a e.val))

def HasPEPSApproximation {L q : ℕ} (Ω : State L q) (C c : ℝ) : Prop :=
  ∃ (D : Edge L → ℕ) (A : (v : Vertex L) → LocalTensor q D v),
    (∀ e, 0 < D e) ∧
    (∀ e, (D e : ℝ) ≤ C * Real.rpow (L : ℝ) c) ∧
    contractPEPS D A ≠ 0 ∧
    ∃ θ : ℝ,
      ‖((‖contractPEPS D A‖⁻¹ : ℝ) : ℂ) • contractPEPS D A - phase θ • Ω‖ ≤
        (L : ℝ)⁻¹

                                                                           
                                                                    
def MainStatement : Prop :=
  ∀ (q : ℕ), 2 ≤ q → ∀ (J Δ : ℝ), 0 < J → 0 < Δ →
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (L : ℕ), 2 ≤ L →
      ∀ (hv : Vertex L → Operator L q) (he : Edge L → Operator L q)
        (Ω : State L q) (E₀ : ℝ),
        IsGridHamiltonian J hv he →
        UniqueGround (Hamiltonian hv he) Ω E₀ →
        FullSystemGap (Hamiltonian hv he) Ω E₀ Δ →
        HasPEPSApproximation Ω C c

end PolynomialPEPS.PhysicalMove

   
                                                                          
                                                                         
                                                                            
                                                                             
  
namespace PolynomialPEPS.PhysicalMove

                                                                               
def joinConfigurations {L q : ℕ} (A : Finset (Vertex L))
    (x : RegionConfiguration q A) (z : RegionConfiguration q Aᶜ) :
    Configuration L q := by
  classical
  exact fun v => if h : v ∈ A then x ⟨v, h⟩ else z ⟨v, Finset.mem_compl.mpr h⟩

                                                                            
                               
def coefficientMatrix {L q : ℕ} (Ω : State L q) (A : Finset (Vertex L)) :
    Matrix (RegionConfiguration q A) (RegionConfiguration q Aᶜ) ℂ :=
  fun x z => Ω (joinConfigurations A x z)

                                                                            
                                                              
def reducedDensity {L q : ℕ} (Ω : State L q) (A : Finset (Vertex L)) :
    Matrix (RegionConfiguration q A) (RegionConfiguration q A) ℂ :=
  coefficientMatrix Ω A * (coefficientMatrix Ω A).conjTranspose

theorem reducedDensity_isHermitian {L q : ℕ} (Ω : State L q)
    (A : Finset (Vertex L)) : (reducedDensity Ω A).IsHermitian := by
  exact Matrix.isHermitian_mul_conjTranspose_self _

                                                                    
                                                                    
def vonNeumannEntropy {L q : ℕ} (Ω : State L q) (A : Finset (Vertex L)) : ℝ :=
  ∑ i, Real.negMulLog ((reducedDensity_isHermitian Ω A).eigenvalues i)

                                                                               
                                                                          
def boundaryCard {L : ℕ} (A : Finset (Vertex L)) : ℕ := by
  classical
  exact Fintype.card {e : Edge L //
    (e.val.1 ∈ A ∧ e.val.2 ∉ A) ∨ (e.val.1 ∉ A ∧ e.val.2 ∈ A)}

                                                                             
                                                                           
                                                                           
def UniformAreaLaw : Prop :=
  ∀ (q : ℕ), 2 ≤ q → ∀ (J Δ : ℝ), 0 < J → 0 < Δ →
    ∃ C_A : ℝ, 0 < C_A ∧
      ∀ (L : ℕ), 2 ≤ L →
      ∀ (hv : Vertex L → Operator L q) (he : Edge L → Operator L q)
        (Ω : State L q) (E₀ : ℝ),
        IsGridHamiltonian J hv he →
        UniqueGround (Hamiltonian hv he) Ω E₀ →
        FullSystemGap (Hamiltonian hv he) Ω E₀ Δ →
        ∀ A : Finset (Vertex L),
          vonNeumannEntropy Ω A ≤ C_A * (boundaryCard A : ℝ)

end PolynomialPEPS.PhysicalMove

end
end

end OAI
