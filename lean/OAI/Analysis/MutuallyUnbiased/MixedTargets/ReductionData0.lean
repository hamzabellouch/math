import OAI.Analysis.MutuallyUnbiased.Certificate.MixedTargetBasic
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values0

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

def reducedTerm0 : Integer.Sparse Master := [(Sum.inl 0, 2563162779156553728000), (Sum.inl 1, 3495221971577118720000), (Sum.inl 2, 2330147981051412480000)]

def originalTerm0 : Integer.Sparse OriginalKey := [(Sum.inl 0, 445921053840)]

theorem reducedTermArithmetic0 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm0 x = (16777065463570169856000 : ℝ) * Sparse.eval nodeValue0 x := by
  norm_num [reducedTerm0, nodeValue0, Integer.Sparse.eval, Sparse.eval]
  ring

def reducedTerm1 : Integer.Sparse Master := [(Sum.inl 0, 4056921058202320896000), (Sum.inl 1, -5071151322752901120000), (Sum.inl 2, -5071151322752901120000)]

def originalTerm1 : Integer.Sparse OriginalKey := [(Sum.inl 1, 646978406640)]

theorem reducedTermArithmetic1 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm1 x = (24341526349213925376000 : ℝ) * Sparse.eval nodeValue1 x := by
  norm_num [reducedTerm1, nodeValue1, Integer.Sparse.eval, Sparse.eval]
  ring

def reducedTerm2 : Integer.Sparse Master := [(Sum.inl 0, 469974932497760256000), (Sum.inl 2, 2349874662488801280000)]

def originalTerm2 : Integer.Sparse OriginalKey := [(Sum.inl 2, 74949359040)]

theorem reducedTermArithmetic2 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm2 x = (2819849594986561536000 : ℝ) * Sparse.eval nodeValue2 x := by
  norm_num [reducedTerm2, nodeValue2, Integer.Sparse.eval, Sparse.eval]
  ring

def reducedTerm3 : Integer.Sparse Master := [(Sum.inl 0, 2212213202121129984000), (Sum.inl 1, 4147899753977118720000), (Sum.inl 2, -1382633251325706240000)]

def originalTerm3 : Integer.Sparse OriginalKey := [(Sum.inl 3, 529189803840)]

theorem reducedTermArithmetic3 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm3 x = (19909918819090169856000 : ℝ) * Sparse.eval nodeValue3 x := by
  norm_num [reducedTerm3, nodeValue3, Integer.Sparse.eval, Sparse.eval]
  ring

def reducedTerm4 : Integer.Sparse Master := [(Sum.inl 0, 7396337533618446336000), (Sum.inl 1, -6723943212380405760000), (Sum.inl 2, 3361971606190202880000)]

def originalTerm4 : Integer.Sparse OriginalKey := [(Sum.inl 4, 1286762844080)]

theorem reducedTermArithmetic4 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm4 x = (48412391129138921472000 : ℝ) * Sparse.eval nodeValue4 x := by
  norm_num [reducedTerm4, nodeValue4, Integer.Sparse.eval, Sparse.eval]
  ring

def reducedTerm5 : Integer.Sparse Master := [(Sum.inl 0, 1692420459861196800000), (Sum.inl 1, -1692420459861196800000)]

def originalTerm5 : Integer.Sparse OriginalKey := [(Sum.inl 5, 215919309600)]

theorem reducedTermArithmetic5 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm5 x = (8123618207333744640000 : ℝ) * Sparse.eval nodeValue5 x := by
  norm_num [reducedTerm5, nodeValue5, Integer.Sparse.eval, Sparse.eval]
  ring

def reducedTerm6 : Integer.Sparse Master := [(Sum.inl 0, 1316966819005071360000), (Sum.inl 1, 6584834095025356800000)]

def originalTerm6 : Integer.Sparse OriginalKey := [(Sum.inl 6, 210023582400)]

theorem reducedTermArithmetic6 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm6 x = (7901800914030428160000 : ℝ) * Sparse.eval nodeValue6 x := by
  norm_num [reducedTerm6, nodeValue6, Integer.Sparse.eval, Sparse.eval]
  ring

def reducedTerm7 : Integer.Sparse Master := [(Sum.inl 0, 1737686641551114240000), (Sum.inl 1, 457285958302924800000)]

def originalTerm7 : Integer.Sparse OriginalKey := [(Sum.inl 7, 175021876800)]

theorem reducedTermArithmetic7 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm7 x = (6584917799562117120000 : ℝ) * Sparse.eval nodeValue7 x := by
  norm_num [reducedTerm7, nodeValue7, Integer.Sparse.eval, Sparse.eval]
  ring

def reducedTerm8 : Integer.Sparse Master := [(Sum.inl 0, -8075576528732160000), (Sum.inl 1, 2523617665228800000), (Sum.inl 2, 30283411982745600000), (Sum.inl 5, -151417059913728000000), (Sum.inl 6, 30283411982745600000), (Sum.inl 7, 242267295861964800000), (Sum.inl 9, -100944706609152000000), (Sum.inl 35, 121133647930982400000), (Sum.inl 58, 2523617665228800000), (Sum.inl 69, 363400943792947200000), (Sum.inl 70, 323023061149286400000), (Sum.inl 71, 242267295861964800000), (Sum.inl 257, 80755765287321600000)]

def originalTerm8 : Integer.Sparse OriginalKey := [(Sum.inl 8, -11590689600)]

theorem reducedTermArithmetic8 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm8 x = (-436081132551536640000 : ℝ) * Sparse.eval nodeValue8 x := by
  norm_num [reducedTerm8, nodeValue8, Integer.Sparse.eval, Sparse.eval]
  ring

def reducedTerm9 : Integer.Sparse Master := [(Sum.inl 0, 8075576528732160000), (Sum.inl 1, 7570852995686400000), (Sum.inl 2, -7570852995686400000), (Sum.inl 5, -40377882643660800000), (Sum.inl 6, 20188941321830400000), (Sum.inl 9, -60566823965491200000), (Sum.inl 58, 5047235330457600000), (Sum.inl 69, 40377882643660800000), (Sum.inl 70, 40377882643660800000), (Sum.inl 71, 80755765287321600000)]

def originalTerm9 : Integer.Sparse OriginalKey := [(Sum.inl 9, 11590689600)]

theorem reducedTermArithmetic9 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm9 x = (436081132551536640000 : ℝ) * Sparse.eval nodeValue9 x := by
  norm_num [reducedTerm9, nodeValue9, Integer.Sparse.eval, Sparse.eval]
  ring

def reducedTerm10 : Integer.Sparse Master := [(Sum.inl 0, 82045141724528640000), (Sum.inl 1, -58603672660377600000), (Sum.inl 2, -136741902874214400000), (Sum.inl 3, -625105841710694400000), (Sum.inl 5, 937658762566041600000), (Sum.inl 6, -117207345320755200000), (Sum.inl 7, -1875317525132083200000), (Sum.inl 8, -625105841710694400000), (Sum.inl 9, 625105841710694400000), (Sum.inl 35, -1250211683421388800000), (Sum.inl 52, -625105841710694400000), (Sum.inl 58, -19534557553459200000), (Sum.inl 69, -2500423366842777600000), (Sum.inl 70, -1562764604276736000000), (Sum.inl 71, -1875317525132083200000), (Sum.inl 256, 1875317525132083200000), (Sum.inl 257, -625105841710694400000), (Sum.inl 495, -625105841710694400000)]

def originalTerm10 : Integer.Sparse OriginalKey := [(Sum.inl 10, 89720006400)]

theorem reducedTermArithmetic10 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm10 x = (3375571545237749760000 : ℝ) * Sparse.eval nodeValue10 x := by
  norm_num [reducedTerm10, nodeValue10, Integer.Sparse.eval, Sparse.eval]
  ring

def reducedTerm11 : Integer.Sparse Master := [(Sum.inl 0, 78138230213836800000), (Sum.inl 1, 97672787767296000000), (Sum.inl 2, 253949248194969600000), (Sum.inl 5, -312552920855347200000), (Sum.inl 6, 117207345320755200000), (Sum.inl 9, -390691151069184000000), (Sum.inl 52, 312552920855347200000), (Sum.inl 58, 39069115106918400000), (Sum.inl 69, 625105841710694400000), (Sum.inl 71, 625105841710694400000), (Sum.inl 495, 312552920855347200000)]

def originalTerm11 : Integer.Sparse OriginalKey := [(Sum.inl 11, 89720006400)]

theorem reducedTermArithmetic11 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm11 x = (3375571545237749760000 : ℝ) * Sparse.eval nodeValue11 x := by
  norm_num [reducedTerm11, nodeValue11, Integer.Sparse.eval, Sparse.eval]
  ring

def reducedTerm12 : Integer.Sparse Master := [(Sum.inl 0, -60247541355724800000), (Sum.inl 1, 123233607318528000000), (Sum.inl 2, 41077869106176000000), (Sum.inl 5, 164311476424704000000), (Sum.inl 7, -438163937132544000000), (Sum.inl 9, 219081968566272000000), (Sum.inl 35, -219081968566272000000), (Sum.inl 69, -657245905698816000000), (Sum.inl 70, -657245905698816000000), (Sum.inl 71, -219081968566272000000), (Sum.inl 257, -219081968566272000000)]

def originalTerm12 : Integer.Sparse OriginalKey := [(Sum.inl 12, -62888664000)]

theorem reducedTermArithmetic12 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm12 x = (-2366085260515737600000 : ℝ) * Sparse.eval nodeValue12 x := by
  norm_num [reducedTerm12, nodeValue12, Integer.Sparse.eval, Sparse.eval]
  ring

def reducedTerm13 : Integer.Sparse Master := [(Sum.inl 0, -25396268601876480000), (Sum.inl 1, 57718792276992000000), (Sum.inl 2, 34631275366195200000), (Sum.inl 5, -92350067643187200000), (Sum.inl 6, 46175033821593600000), (Sum.inl 9, -138525101464780800000), (Sum.inl 58, 34631275366195200000)]

def originalTerm13 : Integer.Sparse OriginalKey := [(Sum.inl 13, -26509586400)]

theorem reducedTermArithmetic13 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm13 x = (-997380730546421760000 : ℝ) * Sparse.eval nodeValue13 x := by
  norm_num [reducedTerm13, nodeValue13, Integer.Sparse.eval, Sparse.eval]
  ring

def reducedTerm14 : Integer.Sparse Master := [(Sum.inl 0, -52112700867870720000), (Sum.inl 1, -11843795651788800000), (Sum.inl 2, 11843795651788800000), (Sum.inl 5, 94750365214310400000), (Sum.inl 6, -71062773910732800000), (Sum.inl 9, 189500730428620800000), (Sum.inl 35, -379001460857241600000), (Sum.inl 58, -23687591303577600000), (Sum.inl 69, -189500730428620800000), (Sum.inl 70, -189500730428620800000), (Sum.inl 257, -379001460857241600000), (Sum.inl 495, -379001460857241600000)]

def originalTerm14 : Integer.Sparse OriginalKey := [(Sum.inl 14, -54397209600)]

theorem reducedTermArithmetic14 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm14 x = (-2046607888629104640000 : ℝ) * Sparse.eval nodeValue14 x := by
  norm_num [reducedTerm14, nodeValue14, Integer.Sparse.eval, Sparse.eval]
  ring

def reducedTerm15 : Integer.Sparse Master := [(Sum.inl 0, -78138230213836800000), (Sum.inl 1, -58603672660377600000), (Sum.inl 2, -136741902874214400000), (Sum.inl 5, 234414690641510400000), (Sum.inl 7, -312552920855347200000), (Sum.inl 8, -312552920855347200000), (Sum.inl 9, 312552920855347200000), (Sum.inl 69, -625105841710694400000), (Sum.inl 70, -312552920855347200000), (Sum.inl 71, -937658762566041600000), (Sum.inl 256, 937658762566041600000)]

def originalTerm15 : Integer.Sparse OriginalKey := [(Sum.inl 15, -89720006400)]

theorem reducedTermArithmetic15 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm15 x = (-3375571545237749760000 : ℝ) * Sparse.eval nodeValue15 x := by
  norm_num [reducedTerm15, nodeValue15, Integer.Sparse.eval, Sparse.eval]
  ring

def reducedTerm16 : Integer.Sparse Master := [(Sum.inl 0, 52112700867870720000), (Sum.inl 2, -47375182607155200000), (Sum.inl 5, 94750365214310400000), (Sum.inl 6, -94750365214310400000), (Sum.inl 9, 189500730428620800000), (Sum.inl 58, -71062773910732800000), (Sum.inl 495, -379001460857241600000)]

def originalTerm16 : Integer.Sparse OriginalKey := [(Sum.inl 16, 54397209600)]

theorem reducedTermArithmetic16 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm16 x = (2046607888629104640000 : ℝ) * Sparse.eval nodeValue16 x := by
  norm_num [reducedTerm16, nodeValue16, Integer.Sparse.eval, Sparse.eval]
  ring

def reducedTerm17 : Integer.Sparse Master := [(Sum.inl 0, -15941264449904640000), (Sum.inl 1, 36230146477056000000), (Sum.inl 2, 14492058590822400000), (Sum.inl 9, -86952351544934400000), (Sum.inl 69, 115936468726579200000), (Sum.inl 70, 115936468726579200000), (Sum.inl 71, 115936468726579200000)]

def originalTerm17 : Integer.Sparse OriginalKey := [(Sum.inl 17, -16640095200)]

theorem reducedTermArithmetic17 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm17 x = (-626056931123527680000 : ℝ) * Sparse.eval nodeValue17 x := by
  norm_num [reducedTerm17, nodeValue17, Integer.Sparse.eval, Sparse.eval]
  ring

def reducedTerm18 : Integer.Sparse Master := [(Sum.inl 0, -78138230213836800000), (Sum.inl 1, -39069115106918400000), (Sum.inl 2, -117207345320755200000), (Sum.inl 9, -468829381283020800000), (Sum.inl 69, 625105841710694400000), (Sum.inl 71, 1250211683421388800000)]

def originalTerm18 : Integer.Sparse OriginalKey := [(Sum.inl 18, -89720006400)]

theorem reducedTermArithmetic18 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm18 x = (-3375571545237749760000 : ℝ) * Sparse.eval nodeValue18 x := by
  norm_num [reducedTerm18, nodeValue18, Integer.Sparse.eval, Sparse.eval]
  ring

def reducedTerm19 : Integer.Sparse Master := [(Sum.inl 0, -38820060750643200000), (Sum.inl 1, 97050151876608000000), (Sum.inl 2, 97050151876608000000), (Sum.inl 9, -194100303753216000000), (Sum.inl 69, 258800405004288000000), (Sum.inl 70, 258800405004288000000), (Sum.inl 257, 258800405004288000000)]

def originalTerm19 : Integer.Sparse OriginalKey := [(Sum.inl 19, -37145028000)]

theorem reducedTermArithmetic19 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm19 x = (-1397522187023155200000 : ℝ) * Sparse.eval nodeValue19 x := by
  norm_num [reducedTerm19, nodeValue19, Integer.Sparse.eval, Sparse.eval]
  ring

def reducedTerm20 : Integer.Sparse Master := [(Sum.inl 0, 23884897183580160000), (Sum.inl 1, -59712242958950400000), (Sum.inl 2, -59712242958950400000), (Sum.inl 9, -238848971835801600000), (Sum.inl 58, 119424485917900800000)]

def originalTerm20 : Integer.Sparse OriginalKey := [(Sum.inl 20, 22854296400)]

theorem reducedTermArithmetic20 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm20 x = (859856298608885760000 : ℝ) * Sparse.eval nodeValue20 x := by
  norm_num [reducedTerm20, nodeValue20, Integer.Sparse.eval, Sparse.eval]
  ring

def reducedTerm21 : Integer.Sparse Master := [(Sum.inl 0, -34582896065249280000), (Sum.inl 1, -54035775101952000000), (Sum.inl 2, -54035775101952000000), (Sum.inl 3, 518743440978739200000), (Sum.inl 5, 345828960652492800000), (Sum.inl 6, -129685860244684800000), (Sum.inl 7, 518743440978739200000), (Sum.inl 9, 821343781549670400000), (Sum.inl 35, 864572401631232000000), (Sum.inl 52, 1037486881957478400000), (Sum.inl 58, -43228620081561600000), (Sum.inl 69, 1037486881957478400000), (Sum.inl 70, 518743440978739200000), (Sum.inl 71, 518743440978739200000), (Sum.inl 256, -1556230322936217600000), (Sum.inl 257, 345828960652492800000), (Sum.inl 495, 518743440978739200000)]

def originalTerm21 : Integer.Sparse OriginalKey := [(Sum.inl 21, -49636036800)]

theorem reducedTermArithmetic21 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm21 x = (-1867476387523461120000 : ℝ) * Sparse.eval nodeValue21 x := by
  norm_num [reducedTerm21, nodeValue21, Integer.Sparse.eval, Sparse.eval]
  ring

def reducedTerm22 : Integer.Sparse Master := [(Sum.inl 0, -36853560336015360000), (Sum.inl 1, 25416248507596800000), (Sum.inl 2, -12708124253798400000), (Sum.inl 6, -57186559142092800000), (Sum.inl 7, 304994982091161600000), (Sum.inl 8, 609989964182323200000), (Sum.inl 9, 406659976121548800000), (Sum.inl 58, -25416248507596800000), (Sum.inl 69, 609989964182323200000), (Sum.inl 70, 203329988060774400000), (Sum.inl 71, 1219979928364646400000)]

def originalTerm22 : Integer.Sparse OriginalKey := [(Sum.inl 22, -29183486400)]

theorem reducedTermArithmetic22 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm22 x = (-1097981935528181760000 : ℝ) * Sparse.eval nodeValue22 x := by
  norm_num [reducedTerm22, nodeValue22, Integer.Sparse.eval, Sparse.eval]
  ring

def reducedTerm23 : Integer.Sparse Master := [(Sum.inl 0, 34582896065249280000), (Sum.inl 1, 32421465061171200000), (Sum.inl 2, -75650085142732800000), (Sum.inl 5, 43228620081561600000), (Sum.inl 6, -32421465061171200000), (Sum.inl 9, 216143100407808000000), (Sum.inl 52, 345828960652492800000), (Sum.inl 58, -10807155020390400000), (Sum.inl 69, 345828960652492800000), (Sum.inl 71, 172914480326246400000), (Sum.inl 256, -518743440978739200000), (Sum.inl 495, 172914480326246400000)]

def originalTerm23 : Integer.Sparse OriginalKey := [(Sum.inl 24, 49636036800)]

theorem reducedTermArithmetic23 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm23 x = (1867476387523461120000 : ℝ) * Sparse.eval nodeValue24 x := by
  norm_num [reducedTerm23, nodeValue24, Integer.Sparse.eval, Sparse.eval]
  ring

def reducedTerm24 : Integer.Sparse Master := [(Sum.inl 0, 43391874277785600000), (Sum.inl 1, 32142129094656000000), (Sum.inl 2, 48213193641984000000), (Sum.inl 6, -16071064547328000000), (Sum.inl 8, 257137032757248000000), (Sum.inl 9, 128568516378624000000), (Sum.inl 58, -8035532273664000000), (Sum.inl 69, 128568516378624000000), (Sum.inl 71, 514274065514496000000)]

def originalTerm24 : Integer.Sparse OriginalKey := [(Sum.inl 26, 36906288000)]

theorem reducedTermArithmetic24 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm24 x = (1388539976889139200000 : ℝ) * Sparse.eval nodeValue26 x := by
  norm_num [reducedTerm24, nodeValue26, Integer.Sparse.eval, Sparse.eval]
  ring

def reducedTerm25 : Integer.Sparse Master := [(Sum.inl 0, -14475351711744000000), (Sum.inl 1, 36188379279360000000), (Sum.inl 2, 23028968632320000000), (Sum.inl 3, -52637642588160000000), (Sum.inl 5, -39478231941120000000), (Sum.inl 6, 9869557985280000000), (Sum.inl 7, -52637642588160000000), (Sum.inl 9, -65797053235200000000), (Sum.inl 35, -105275285176320000000), (Sum.inl 52, -52637642588160000000), (Sum.inl 58, 3289852661760000000), (Sum.inl 69, -52637642588160000000), (Sum.inl 70, -52637642588160000000), (Sum.inl 256, 157912927764480000000), (Sum.inl 257, -52637642588160000000), (Sum.inl 495, -52637642588160000000)]

def originalTerm25 : Integer.Sparse OriginalKey := [(Sum.inl 27, -15109920000)]

theorem reducedTermArithmetic25 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm25 x = (-568486539952128000000 : ℝ) * Sparse.eval nodeValue27 x := by
  norm_num [reducedTerm25, nodeValue27, Integer.Sparse.eval, Sparse.eval]
  ring

def reducedTerm26 : Integer.Sparse Master := [(Sum.inl 0, 27464140247040000000), (Sum.inl 1, -64082993909760000000), (Sum.inl 2, -36618853662720000000), (Sum.inl 5, 36618853662720000000), (Sum.inl 6, 9154713415680000000), (Sum.inl 58, 9154713415680000000), (Sum.inl 71, -146475414650880000000)]

def originalTerm26 : Integer.Sparse OriginalKey := [(Sum.inl 28, 21023280000)]

theorem reducedTermArithmetic26 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm26 x = (790967239114752000000 : ℝ) * Sparse.eval nodeValue28 x := by
  norm_num [reducedTerm26, nodeValue28, Integer.Sparse.eval, Sparse.eval]
  ring

def reducedTerm27 : Integer.Sparse Master := [(Sum.inl 0, -20421240724684800000), (Sum.inl 1, 18564764295168000000), (Sum.inl 2, -120670967918592000000), (Sum.inl 5, 37129528590336000000), (Sum.inl 9, 74259057180672000000), (Sum.inl 35, 148518114361344000000), (Sum.inl 70, 148518114361344000000), (Sum.inl 257, 148518114361344000000)]

def originalTerm27 : Integer.Sparse OriginalKey := [(Sum.inl 29, -21316464000)]

theorem reducedTermArithmetic27 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm27 x = (-801997817551257600000 : ℝ) * Sparse.eval nodeValue29 x := by
  norm_num [reducedTerm27, nodeValue29, Integer.Sparse.eval, Sparse.eval]
  ring

def reducedTerm28 : Integer.Sparse Master := [(Sum.inl 0, 8667910534348800000), (Sum.inl 1, -20225124580147200000), (Sum.inl 2, -11557214045798400000), (Sum.inl 9, -23114428091596800000), (Sum.inl 69, -46228856183193600000), (Sum.inl 71, -46228856183193600000)]

def originalTerm28 : Integer.Sparse OriginalKey := [(Sum.inl 30, 6635121600)]

theorem reducedTermArithmetic28 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm28 x = (249635823389245440000 : ℝ) * Sparse.eval nodeValue30 x := by
  norm_num [reducedTerm28, nodeValue30, Integer.Sparse.eval, Sparse.eval]
  ring

def reducedTerm29 : Integer.Sparse Master := [(Sum.inl 0, -34488646944030720000), (Sum.inl 1, 86221617360076800000), (Sum.inl 2, 71851347800064000000), (Sum.inl 6, -28740539120025600000), (Sum.inl 9, 57481078240051200000), (Sum.inl 35, 229924312960204800000), (Sum.inl 58, -14370269560012800000), (Sum.inl 257, 229924312960204800000), (Sum.inl 495, 229924312960204800000)]

def originalTerm29 : Integer.Sparse OriginalKey := [(Sum.inl 32, -33000508800)]

theorem reducedTermArithmetic29 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm29 x = (-1241591289985105920000 : ℝ) * Sparse.eval nodeValue32 x := by
  norm_num [reducedTerm29, nodeValue32, Integer.Sparse.eval, Sparse.eval]
  ring

def reducedTerm30 : Integer.Sparse Master := [(Sum.inl 0, -71713207222272000000), (Sum.inl 1, -268924527083520000000), (Sum.inl 2, 89641509027840000000), (Sum.inl 5, 119522012037120000000), (Sum.inl 7, 478088048148480000000), (Sum.inl 9, 239044024074240000000), (Sum.inl 69, 478088048148480000000), (Sum.inl 70, 478088048148480000000)]

def originalTerm30 : Integer.Sparse OriginalKey := [(Sum.inl 33, -68618880000)]

theorem reducedTermArithmetic30 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm30 x = (-2581675460001792000000 : ℝ) * Sparse.eval nodeValue33 x := by
  norm_num [reducedTerm30, nodeValue33, Integer.Sparse.eval, Sparse.eval]
  ring

def reducedTerm31 : Integer.Sparse Master := [(Sum.inl 0, -9416232821882880000), (Sum.inl 2, -6725880587059200000), (Sum.inl 5, 13451761174118400000), (Sum.inl 8, 53807044696473600000), (Sum.inl 9, 26903522348236800000), (Sum.inl 71, 107614089392947200000)]

def originalTerm31 : Integer.Sparse OriginalKey := [(Sum.inl 34, -7722801600)]

theorem reducedTermArithmetic31 (x : Master → ℝ) :
    Integer.Sparse.eval reducedTerm31 x = (-290558041360957440000 : ℝ) * Sparse.eval nodeValue34 x := by
  norm_num [reducedTerm31, nodeValue34, Integer.Sparse.eval, Sparse.eval]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
